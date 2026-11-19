Require Import RegisterInvariants CoreSocModel ComparisonNodes ScalarNodeFrames FormalTypedNodeFrames FormalTypedNodeEquation.
From Coq Require Import ZArith.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths Firrtl_with_implicit_widths HiEnv_with_implicit_widths
 HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Definition pc_jump_expr_7774 := (@Eprim_binop VarOrder.T Bdshr (@Eref VarOrder.T (@Eid VarOrder.T 1155)) (@Econst VarOrder.T (Fuint 1) [::true])).
Definition pc_jump_tail_7774 := match straight_drop 8281 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma pc_jump_position_7774 : straight_drop 8280 flat_statements = Some (@Qcons VarOrder.T (@Snode VarOrder.T 7774 pc_jump_expr_7774) pc_jump_tail_7774).
Proof. vm_compute. reflexivity. Qed.
Lemma pc_jump_suffix_7774 : formal_typed_suffix_safe flat_memories 7774 pc_jump_tail_7774.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma pc_jump_nonregister_7774 : has_register 7774 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem pc_jump_node_7774 invalid old current result value :
 eval_hfexpr_with_memory flat_memories pc_jump_expr_7774 old old = Some value ->
 type_of_val value = Gtyp (Fuint 32) ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 7774 result = Some value.
Proof. intros Eval Typed Step. eapply formal_combinational_known_node;
 [exact pc_jump_position_7774|exact pc_jump_suffix_7774|exact pc_jump_nonregister_7774|exact Eval|exact Typed|exact Step]. Qed.
Definition pc_jump_expr_7775 := (@Eprim_binop VarOrder.T Bdshl (@Eref VarOrder.T (@Eid VarOrder.T 7774)) (@Econst VarOrder.T (Fuint 1) [::true])).
Definition pc_jump_tail_7775 := match straight_drop 8282 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma pc_jump_position_7775 : straight_drop 8281 flat_statements = Some (@Qcons VarOrder.T (@Snode VarOrder.T 7775 pc_jump_expr_7775) pc_jump_tail_7775).
Proof. vm_compute. reflexivity. Qed.
Lemma pc_jump_suffix_7775 : formal_typed_suffix_safe flat_memories 7775 pc_jump_tail_7775.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma pc_jump_nonregister_7775 : has_register 7775 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem pc_jump_node_7775 invalid old current result value :
 eval_hfexpr_with_memory flat_memories pc_jump_expr_7775 old old = Some value ->
 type_of_val value = Gtyp (Fuint 33) ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 7775 result = Some value.
Proof. intros Eval Typed Step. eapply formal_combinational_known_node;
 [exact pc_jump_position_7775|exact pc_jump_suffix_7775|exact pc_jump_nonregister_7775|exact Eval|exact Typed|exact Step]. Qed.
Print Assumptions pc_jump_node_7775.
