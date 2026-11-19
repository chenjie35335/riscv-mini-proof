Require Import RegisterInvariants CoreSocModel ComparisonNodes ScalarNodeFrames FormalTypedNodeFrames FormalTypedNodeEquation.
From Coq Require Import ZArith.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths Firrtl_with_implicit_widths HiEnv_with_implicit_widths
 HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Definition rf_source_expr_8092 := (@Eref VarOrder.T (@Eid VarOrder.T 8091)).
Definition rf_source_tail_8092 := match straight_drop 8599 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma rf_source_position_8092 : straight_drop 8598 flat_statements = Some (@Qcons VarOrder.T (@Snode VarOrder.T 8092 rf_source_expr_8092) rf_source_tail_8092).
Proof. vm_compute. reflexivity. Qed.
Lemma rf_source_suffix_8092 : formal_typed_suffix_safe flat_memories 8092 rf_source_tail_8092.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma rf_source_nonregister_8092 : has_register 8092 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem rf_source_node_8092 invalid old current result value :
 eval_hfexpr_with_memory flat_memories rf_source_expr_8092 old old = Some value ->
 type_of_val value = Gtyp (Fuint 32) ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 8092 result = Some value.
Proof. intros Eval Typed Step. eapply formal_combinational_known_node;
 [exact rf_source_position_8092|exact rf_source_suffix_8092|exact rf_source_nonregister_8092|exact Eval|exact Typed|exact Step]. Qed.
Definition rf_source_expr_1086 := (@Eref VarOrder.T (@Eid VarOrder.T 788)).
Definition rf_source_tail_1086 := match straight_drop 1096 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma rf_source_position_1086 : straight_drop 1095 flat_statements = Some (@Qcons VarOrder.T (@Snode VarOrder.T 1086 rf_source_expr_1086) rf_source_tail_1086).
Proof. vm_compute. reflexivity. Qed.
Lemma rf_source_suffix_1086 : formal_typed_suffix_safe flat_memories 1086 rf_source_tail_1086.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma rf_source_nonregister_1086 : has_register 1086 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem rf_source_node_1086 invalid old current result value :
 eval_hfexpr_with_memory flat_memories rf_source_expr_1086 old old = Some value ->
 type_of_val value = Gtyp (Fuint 32) ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 1086 result = Some value.
Proof. intros Eval Typed Step. eapply formal_combinational_known_node;
 [exact rf_source_position_1086|exact rf_source_suffix_1086|exact rf_source_nonregister_1086|exact Eval|exact Typed|exact Step]. Qed.
Print Assumptions rf_source_node_1086.
