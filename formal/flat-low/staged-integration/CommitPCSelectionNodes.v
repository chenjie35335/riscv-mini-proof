Require Import RegisterInvariants CoreSocModel ComparisonNodes ScalarNodeFrames FormalTypedNodeFrames FormalTypedNodeEquation.
From Coq Require Import ZArith.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths Firrtl_with_implicit_widths HiEnv_with_implicit_widths
 HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Definition commit_pc_source_expr_7860 := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 7855)) (@Eref VarOrder.T (@Eid VarOrder.T 7749)) (@Eref VarOrder.T (@Eid VarOrder.T 7751))).
Definition commit_pc_source_tail_7860 := match straight_drop 8367 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma commit_pc_source_position_7860 : straight_drop 8366 flat_statements = Some (@Qcons VarOrder.T (@Snode VarOrder.T 7860 commit_pc_source_expr_7860) commit_pc_source_tail_7860).
Proof. vm_compute. reflexivity. Qed.
Lemma commit_pc_source_suffix_7860 : formal_typed_suffix_safe flat_memories 7860 commit_pc_source_tail_7860.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma commit_pc_source_nonregister_7860 : has_register 7860 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem commit_pc_source_node_7860 invalid old current result value :
 eval_hfexpr_with_memory flat_memories commit_pc_source_expr_7860 old old = Some value ->
 type_of_val value = Gtyp (Fuint 32) ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 7860 result = Some value.
Proof. intros Eval Typed Step. eapply formal_combinational_known_node;
 [exact commit_pc_source_position_7860|exact commit_pc_source_suffix_7860|exact commit_pc_source_nonregister_7860|exact Eval|exact Typed|exact Step]. Qed.
Definition commit_pc_source_expr_7877 := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 7852)) (@Eref VarOrder.T (@Eid VarOrder.T 7751)) (@Eref VarOrder.T (@Eid VarOrder.T 7860))).
Definition commit_pc_source_tail_7877 := match straight_drop 8384 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma commit_pc_source_position_7877 : straight_drop 8383 flat_statements = Some (@Qcons VarOrder.T (@Snode VarOrder.T 7877 commit_pc_source_expr_7877) commit_pc_source_tail_7877).
Proof. vm_compute. reflexivity. Qed.
Lemma commit_pc_source_suffix_7877 : formal_typed_suffix_safe flat_memories 7877 commit_pc_source_tail_7877.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma commit_pc_source_nonregister_7877 : has_register 7877 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem commit_pc_source_node_7877 invalid old current result value :
 eval_hfexpr_with_memory flat_memories commit_pc_source_expr_7877 old old = Some value ->
 type_of_val value = Gtyp (Fuint 32) ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 7877 result = Some value.
Proof. intros Eval Typed Step. eapply formal_combinational_known_node;
 [exact commit_pc_source_position_7877|exact commit_pc_source_suffix_7877|exact commit_pc_source_nonregister_7877|exact Eval|exact Typed|exact Step]. Qed.
Print Assumptions commit_pc_source_node_7877.
