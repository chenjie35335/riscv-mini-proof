Require Import RegisterInvariants CoreSocModel ComparisonNodes ScalarNodeFrames FormalTypedNodeFrames FormalTypedNodeEquation.
From Coq Require Import ZArith.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths Firrtl_with_implicit_widths HiEnv_with_implicit_widths
 HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Definition pc_normal_expr_7769 := (@Eprim_binop VarOrder.T Badd (@Eref VarOrder.T (@Eid VarOrder.T 7768)) (@Econst VarOrder.T (Fuint 3) [::false; false; true])).
Definition pc_normal_tail_7769 := match straight_drop 8276 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma pc_normal_position_7769 : straight_drop 8275 flat_statements = Some (@Qcons VarOrder.T (@Snode VarOrder.T 7769 pc_normal_expr_7769) pc_normal_tail_7769).
Proof. vm_compute. reflexivity. Qed.
Lemma pc_normal_suffix_7769 : formal_typed_suffix_safe flat_memories 7769 pc_normal_tail_7769.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma pc_normal_nonregister_7769 : has_register 7769 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem pc_normal_node_7769 invalid old current result value :
 eval_hfexpr_with_memory flat_memories pc_normal_expr_7769 old old = Some value ->
 type_of_val value = Gtyp (Fuint 34) ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 7769 result = Some value.
Proof. intros Eval Typed Step. eapply formal_combinational_known_node;
 [exact pc_normal_position_7769|exact pc_normal_suffix_7769|exact pc_normal_nonregister_7769|exact Eval|exact Typed|exact Step]. Qed.
Definition pc_normal_expr_7770 := (@Eprim_unop VarOrder.T (Utail 1) (@Eref VarOrder.T (@Eid VarOrder.T 7769))).
Definition pc_normal_tail_7770 := match straight_drop 8277 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma pc_normal_position_7770 : straight_drop 8276 flat_statements = Some (@Qcons VarOrder.T (@Snode VarOrder.T 7770 pc_normal_expr_7770) pc_normal_tail_7770).
Proof. vm_compute. reflexivity. Qed.
Lemma pc_normal_suffix_7770 : formal_typed_suffix_safe flat_memories 7770 pc_normal_tail_7770.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma pc_normal_nonregister_7770 : has_register 7770 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem pc_normal_node_7770 invalid old current result value :
 eval_hfexpr_with_memory flat_memories pc_normal_expr_7770 old old = Some value ->
 type_of_val value = Gtyp (Fuint 33) ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 7770 result = Some value.
Proof. intros Eval Typed Step. eapply formal_combinational_known_node;
 [exact pc_normal_position_7770|exact pc_normal_suffix_7770|exact pc_normal_nonregister_7770|exact Eval|exact Typed|exact Step]. Qed.
Print Assumptions pc_normal_node_7770.
