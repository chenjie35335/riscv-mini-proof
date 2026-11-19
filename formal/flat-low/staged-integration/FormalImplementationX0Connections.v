Require Import FormalDeclaredConnection ScalarNodeFrames FormalStatementSegments FormalTypedNodeFrames FormalTypedNodeEquation CoreSocModel ComparisonNodes RegisterInvariants.
From Coq Require Import ZArith.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory FormalInitialization.
Local Open Scope N_scope.
Definition implementation_x0_decl_819 := match straight_drop 829 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition implementation_x0_tail_819 := match straight_drop 1161 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition implementation_x0_mid_819 := take_statements 331 implementation_x0_decl_819.
Lemma implementation_x0_position_819 : straight_drop 828 flat_statements = Some (@Qcons VarOrder.T (@Swire VarOrder.T 819 (Gtyp (Fuint 32))) implementation_x0_decl_819).
Proof. vm_compute. reflexivity. Qed.
Lemma implementation_x0_split_819 : implementation_x0_decl_819 = statement_append implementation_x0_mid_819 (@Qcons VarOrder.T (@Sfcnct VarOrder.T (@Eid VarOrder.T 819) (@Eref VarOrder.T (@Eid VarOrder.T 1117))) implementation_x0_tail_819).
Proof. vm_compute. reflexivity. Qed.
Lemma implementation_x0_straight_819 : straight_statements implementation_x0_mid_819.
Proof. vm_compute. exact I. Qed.
Lemma implementation_x0_mid_safe_819 : formal_typed_suffix_safe flat_memories 819 implementation_x0_mid_819.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma implementation_x0_tail_safe_819 : formal_typed_suffix_safe flat_memories 819 implementation_x0_tail_819.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma implementation_x0_nonregister_819 : has_register 819 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem implementation_x0_connection_819 invalid old current result source_value value :
 VM.find 1117 old = Some source_value ->
 adapt_hvalue_as_type source_value (Gtyp (Fuint 32)) = Some value ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 819 result = Some value.
Proof.
 intros Source Adapt Step.
 exact (declared_connection_value 828 flat_statements implementation_x0_decl_819 implementation_x0_mid_819 implementation_x0_tail_819
 819 1117 32 source_value value invalid flat_memories old current result
 implementation_x0_position_819 implementation_x0_split_819 implementation_x0_straight_819 implementation_x0_mid_safe_819 implementation_x0_tail_safe_819
 implementation_x0_nonregister_819 (Logic.eq_refl _) Source Adapt Step).
Qed.
Definition implementation_x0_decl_1399 := match straight_drop 1479 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition implementation_x0_tail_1399 := match straight_drop 8888 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition implementation_x0_mid_1399 := take_statements 7408 implementation_x0_decl_1399.
Lemma implementation_x0_position_1399 : straight_drop 1478 flat_statements = Some (@Qcons VarOrder.T (@Swire VarOrder.T 1399 (Gtyp (Fuint 32))) implementation_x0_decl_1399).
Proof. vm_compute. reflexivity. Qed.
Lemma implementation_x0_split_1399 : implementation_x0_decl_1399 = statement_append implementation_x0_mid_1399 (@Qcons VarOrder.T (@Sfcnct VarOrder.T (@Eid VarOrder.T 1399) (@Eref VarOrder.T (@Eid VarOrder.T 8166))) implementation_x0_tail_1399).
Proof. vm_compute. reflexivity. Qed.
Lemma implementation_x0_straight_1399 : straight_statements implementation_x0_mid_1399.
Proof. vm_compute. exact I. Qed.
Lemma implementation_x0_mid_safe_1399 : formal_typed_suffix_safe flat_memories 1399 implementation_x0_mid_1399.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma implementation_x0_tail_safe_1399 : formal_typed_suffix_safe flat_memories 1399 implementation_x0_tail_1399.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma implementation_x0_nonregister_1399 : has_register 1399 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem implementation_x0_connection_1399 invalid old current result source_value value :
 VM.find 8166 old = Some source_value ->
 adapt_hvalue_as_type source_value (Gtyp (Fuint 32)) = Some value ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 1399 result = Some value.
Proof.
 intros Source Adapt Step.
 exact (declared_connection_value 1478 flat_statements implementation_x0_decl_1399 implementation_x0_mid_1399 implementation_x0_tail_1399
 1399 8166 32 source_value value invalid flat_memories old current result
 implementation_x0_position_1399 implementation_x0_split_1399 implementation_x0_straight_1399 implementation_x0_mid_safe_1399 implementation_x0_tail_safe_1399
 implementation_x0_nonregister_1399 (Logic.eq_refl _) Source Adapt Step).
Qed.
Print Assumptions implementation_x0_connection_1399.
