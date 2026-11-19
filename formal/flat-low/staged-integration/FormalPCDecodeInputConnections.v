Require Import FormalDeclaredConnection ScalarNodeFrames FormalStatementSegments FormalTypedNodeFrames FormalTypedNodeEquation CoreSocModel ComparisonNodes RegisterInvariants.
From Coq Require Import ZArith.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory FormalInitialization.
Local Open Scope N_scope.
Definition decode_input_decl_83 := match straight_drop 61 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition decode_input_tail_83 := match straight_drop 8765 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition decode_input_mid_83 := take_statements 8703 decode_input_decl_83.
Lemma decode_input_position_83 : straight_drop 60 flat_statements = Some (@Qcons VarOrder.T (@Swire VarOrder.T 83 (Gtyp (Fuint 32))) decode_input_decl_83).
Proof. vm_compute. reflexivity. Qed.
Lemma decode_input_split_83 : decode_input_decl_83 = statement_append decode_input_mid_83 (@Qcons VarOrder.T (@Sfcnct VarOrder.T (@Eid VarOrder.T 83) (@Eref VarOrder.T (@Eid VarOrder.T 7748))) decode_input_tail_83).
Proof. vm_compute. reflexivity. Qed.
Lemma decode_input_straight_83 : straight_statements decode_input_mid_83.
Proof. vm_compute. exact I. Qed.
Lemma decode_input_mid_safe_83 : formal_typed_suffix_safe flat_memories 83 decode_input_mid_83.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma decode_input_tail_safe_83 : formal_typed_suffix_safe flat_memories 83 decode_input_tail_83.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma decode_input_nonregister_83 : has_register 83 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem decode_input_connection_83 invalid old current result source_value value :
 VM.find 7748 old = Some source_value ->
 adapt_hvalue_as_type source_value (Gtyp (Fuint 32)) = Some value ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 83 result = Some value.
Proof.
 intros Source Adapt Step.
 exact (declared_connection_value 60 flat_statements decode_input_decl_83 decode_input_mid_83 decode_input_tail_83
 83 7748 32 source_value value invalid flat_memories old current result
 decode_input_position_83 decode_input_split_83 decode_input_straight_83 decode_input_mid_safe_83 decode_input_tail_safe_83
 decode_input_nonregister_83 (Logic.eq_refl _) Source Adapt Step).
Qed.
Definition decode_input_decl_8249 := match straight_drop 9010 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition decode_input_tail_8249 := match straight_drop 10006 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition decode_input_mid_8249 := take_statements 995 decode_input_decl_8249.
Lemma decode_input_position_8249 : straight_drop 9009 flat_statements = Some (@Qcons VarOrder.T (@Swire VarOrder.T 8249 (Gtyp (Fuint 32))) decode_input_decl_8249).
Proof. vm_compute. reflexivity. Qed.
Lemma decode_input_split_8249 : decode_input_decl_8249 = statement_append decode_input_mid_8249 (@Qcons VarOrder.T (@Sfcnct VarOrder.T (@Eid VarOrder.T 8249) (@Eref VarOrder.T (@Eid VarOrder.T 83))) decode_input_tail_8249).
Proof. vm_compute. reflexivity. Qed.
Lemma decode_input_straight_8249 : straight_statements decode_input_mid_8249.
Proof. vm_compute. exact I. Qed.
Lemma decode_input_mid_safe_8249 : formal_typed_suffix_safe flat_memories 8249 decode_input_mid_8249.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma decode_input_tail_safe_8249 : formal_typed_suffix_safe flat_memories 8249 decode_input_tail_8249.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma decode_input_nonregister_8249 : has_register 8249 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem decode_input_connection_8249 invalid old current result source_value value :
 VM.find 83 old = Some source_value ->
 adapt_hvalue_as_type source_value (Gtyp (Fuint 32)) = Some value ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 8249 result = Some value.
Proof.
 intros Source Adapt Step.
 exact (declared_connection_value 9009 flat_statements decode_input_decl_8249 decode_input_mid_8249 decode_input_tail_8249
 8249 83 32 source_value value invalid flat_memories old current result
 decode_input_position_8249 decode_input_split_8249 decode_input_straight_8249 decode_input_mid_safe_8249 decode_input_tail_safe_8249
 decode_input_nonregister_8249 (Logic.eq_refl _) Source Adapt Step).
Qed.
Print Assumptions decode_input_connection_8249.
