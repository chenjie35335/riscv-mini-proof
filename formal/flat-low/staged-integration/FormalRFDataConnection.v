Require Import FormalDeclaredUnaryConnection.
Require Import FormalDeclaredConnection ScalarNodeFrames FormalStatementSegments FormalTypedNodeFrames FormalTypedNodeEquation CoreSocModel ComparisonNodes RegisterInvariants.
From Coq Require Import ZArith.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From firrtl Require Import Firrtl_with_implicit_widths Env_with_implicit_widths HiEnv_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory FormalInitialization.
Local Open Scope N_scope.
Definition rf_input_decl_786 := match straight_drop 796 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition rf_input_tail_786 := match straight_drop 8804 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition rf_input_mid_786 := take_statements 8007 rf_input_decl_786.
Lemma rf_input_position_786 : straight_drop 795 flat_statements = Some (@Qcons VarOrder.T (@Swire VarOrder.T 786 (Gtyp (Fuint 32))) rf_input_decl_786).
Proof. vm_compute. reflexivity. Qed.
Lemma rf_input_split_786 : rf_input_decl_786 = statement_append rf_input_mid_786 (@Qcons VarOrder.T (@Sfcnct VarOrder.T (@Eid VarOrder.T 786) (@Eprim_unop VarOrder.T (Uextr 31 0) (@Eref VarOrder.T (@Eid VarOrder.T 7937)))) rf_input_tail_786).
Proof. vm_compute. reflexivity. Qed.
Lemma rf_input_straight_786 : straight_statements rf_input_mid_786.
Proof. vm_compute. exact I. Qed.
Lemma rf_input_mid_safe_786 : formal_typed_suffix_safe flat_memories 786 rf_input_mid_786.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma rf_input_tail_safe_786 : formal_typed_suffix_safe flat_memories 786 rf_input_tail_786.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma rf_input_nonregister_786 : has_register 786 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem rf_input_connection_786 invalid old current result source_value value :
 eval_hfexpr_with_memory flat_memories (@Eprim_unop VarOrder.T (Uextr 31 0) (@Eref VarOrder.T (@Eid VarOrder.T 7937))) old old = Some source_value ->
 adapt_hvalue_as_type source_value (Gtyp (Fuint 32)) = Some value ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 786 result = Some value.
Proof.
 intros Source Adapt Step.
 exact (declared_unary_connection_value 795 flat_statements rf_input_decl_786 rf_input_mid_786 rf_input_tail_786
 786 7937 (Uextr 31 0) 32 source_value value invalid flat_memories old current result
 rf_input_position_786 rf_input_split_786 rf_input_straight_786 rf_input_mid_safe_786 rf_input_tail_safe_786
 rf_input_nonregister_786 (Logic.eq_refl _) Source Adapt Step).
Qed.
Print Assumptions rf_input_connection_786.
