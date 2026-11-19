Require Import RegisterInvariants CoreSocModel ComparisonNodes ScalarNodeFrames FormalTypedNodeFrames FormalTypedNodeEquation.
From Coq Require Import ZArith.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths Firrtl_with_implicit_widths HiEnv_with_implicit_widths
 HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Definition rf_source_expr_8158 := (@Econst VarOrder.T (Fuint 32) [::true; true; false; false; true; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false]).
Definition rf_source_tail_8158 := match straight_drop 8665 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma rf_source_position_8158 : straight_drop 8664 flat_statements = Some (@Qcons VarOrder.T (@Snode VarOrder.T 8158 rf_source_expr_8158) rf_source_tail_8158).
Proof. vm_compute. reflexivity. Qed.
Lemma rf_source_suffix_8158 : formal_typed_suffix_safe flat_memories 8158 rf_source_tail_8158.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma rf_source_nonregister_8158 : has_register 8158 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem rf_source_node_8158 invalid old current result value :
 eval_hfexpr_with_memory flat_memories rf_source_expr_8158 old old = Some value ->
 type_of_val value = Gtyp (Fuint 32) ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 8158 result = Some value.
Proof. intros Eval Typed Step. eapply formal_combinational_known_node;
 [exact rf_source_position_8158|exact rf_source_suffix_8158|exact rf_source_nonregister_8158|exact Eval|exact Typed|exact Step]. Qed.
Definition instruction_nop : seq bool := [::true; true; false; false; true; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false].
Theorem instruction_reset_node_8158 invalid old current result :
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 8158 result = Some (Gval (Fuint 32) instruction_nop).
Proof.
 intro Step. apply (rf_source_node_8158 invalid old current result (Gval (Fuint 32) instruction_nop));
 [reflexivity|reflexivity|exact Step].
Qed.
Definition rf_source_expr_8160 := (@Econst VarOrder.T (Fuint 32) [::true; true; false; false; true; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false]).
Definition rf_source_tail_8160 := match straight_drop 8667 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma rf_source_position_8160 : straight_drop 8666 flat_statements = Some (@Qcons VarOrder.T (@Snode VarOrder.T 8160 rf_source_expr_8160) rf_source_tail_8160).
Proof. vm_compute. reflexivity. Qed.
Lemma rf_source_suffix_8160 : formal_typed_suffix_safe flat_memories 8160 rf_source_tail_8160.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma rf_source_nonregister_8160 : has_register 8160 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem rf_source_node_8160 invalid old current result value :
 eval_hfexpr_with_memory flat_memories rf_source_expr_8160 old old = Some value ->
 type_of_val value = Gtyp (Fuint 32) ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 8160 result = Some value.
Proof. intros Eval Typed Step. eapply formal_combinational_known_node;
 [exact rf_source_position_8160|exact rf_source_suffix_8160|exact rf_source_nonregister_8160|exact Eval|exact Typed|exact Step]. Qed.
Theorem instruction_reset_node_8160 invalid old current result :
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 8160 result = Some (Gval (Fuint 32) instruction_nop).
Proof.
 intro Step. apply (rf_source_node_8160 invalid old current result (Gval (Fuint 32) instruction_nop));
 [reflexivity|reflexivity|exact Step].
Qed.
Print Assumptions instruction_reset_node_8160.
