Require Import FormalDeclaredConnection ScalarNodeFrames FormalStatementSegments FormalTypedNodeFrames FormalTypedNodeEquation CoreSocModel ComparisonNodes RegisterInvariants.
From Coq Require Import ZArith.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory FormalInitialization.
Local Open Scope N_scope.
Definition rf_input_decl_784 := match straight_drop 794 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition rf_input_tail_784 := match straight_drop 8802 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition rf_input_mid_784 := take_statements 8007 rf_input_decl_784.
Lemma rf_input_position_784 : straight_drop 793 flat_statements = Some (@Qcons VarOrder.T (@Swire VarOrder.T 784 (Gtyp (Fuint 1))) rf_input_decl_784).
Proof. vm_compute. reflexivity. Qed.
Lemma rf_input_split_784 : rf_input_decl_784 = statement_append rf_input_mid_784 (@Qcons VarOrder.T (@Sfcnct VarOrder.T (@Eid VarOrder.T 784) (@Eref VarOrder.T (@Eid VarOrder.T 7941))) rf_input_tail_784).
Proof. vm_compute. reflexivity. Qed.
Lemma rf_input_straight_784 : straight_statements rf_input_mid_784.
Proof. vm_compute. exact I. Qed.
Lemma rf_input_mid_safe_784 : formal_typed_suffix_safe flat_memories 784 rf_input_mid_784.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma rf_input_tail_safe_784 : formal_typed_suffix_safe flat_memories 784 rf_input_tail_784.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma rf_input_nonregister_784 : has_register 784 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem rf_input_connection_784 invalid old current result source_value value :
 VM.find 7941 old = Some source_value ->
 adapt_hvalue_as_type source_value (Gtyp (Fuint 1)) = Some value ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 784 result = Some value.
Proof.
 intros Source Adapt Step.
 exact (declared_connection_value 793 flat_statements rf_input_decl_784 rf_input_mid_784 rf_input_tail_784
 784 7941 1 source_value value invalid flat_memories old current result
 rf_input_position_784 rf_input_split_784 rf_input_straight_784 rf_input_mid_safe_784 rf_input_tail_safe_784
 rf_input_nonregister_784 (Logic.eq_refl _) Source Adapt Step).
Qed.
Definition rf_input_decl_785 := match straight_drop 795 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition rf_input_tail_785 := match straight_drop 8803 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition rf_input_mid_785 := take_statements 8007 rf_input_decl_785.
Lemma rf_input_position_785 : straight_drop 794 flat_statements = Some (@Qcons VarOrder.T (@Swire VarOrder.T 785 (Gtyp (Fuint 5))) rf_input_decl_785).
Proof. vm_compute. reflexivity. Qed.
Lemma rf_input_split_785 : rf_input_decl_785 = statement_append rf_input_mid_785 (@Qcons VarOrder.T (@Sfcnct VarOrder.T (@Eid VarOrder.T 785) (@Eref VarOrder.T (@Eid VarOrder.T 7805))) rf_input_tail_785).
Proof. vm_compute. reflexivity. Qed.
Lemma rf_input_straight_785 : straight_statements rf_input_mid_785.
Proof. vm_compute. exact I. Qed.
Lemma rf_input_mid_safe_785 : formal_typed_suffix_safe flat_memories 785 rf_input_mid_785.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma rf_input_tail_safe_785 : formal_typed_suffix_safe flat_memories 785 rf_input_tail_785.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma rf_input_nonregister_785 : has_register 785 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem rf_input_connection_785 invalid old current result source_value value :
 VM.find 7805 old = Some source_value ->
 adapt_hvalue_as_type source_value (Gtyp (Fuint 5)) = Some value ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 785 result = Some value.
Proof.
 intros Source Adapt Step.
 exact (declared_connection_value 794 flat_statements rf_input_decl_785 rf_input_mid_785 rf_input_tail_785
 785 7805 5 source_value value invalid flat_memories old current result
 rf_input_position_785 rf_input_split_785 rf_input_straight_785 rf_input_mid_safe_785 rf_input_tail_safe_785
 rf_input_nonregister_785 (Logic.eq_refl _) Source Adapt Step).
Qed.
Print Assumptions rf_input_connection_785.
