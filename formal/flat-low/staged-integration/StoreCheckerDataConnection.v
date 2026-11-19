Require Import FormalDeclaredConnection ScalarNodeFrames FormalStatementSegments FormalTypedNodeFrames FormalTypedNodeEquation CoreSocModel ComparisonNodes RegisterInvariants.
From Coq Require Import ZArith.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory FormalInitialization.
Local Open Scope N_scope.
Definition store_checker_data_decl_1481 := match straight_drop 1561 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition store_checker_data_tail_1481 := match straight_drop 8970 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition store_checker_data_mid_1481 := take_statements 7408 store_checker_data_decl_1481.
Lemma store_checker_data_position_1481 : straight_drop 1560 flat_statements = Some (@Qcons VarOrder.T (@Swire VarOrder.T 1481 (Gtyp (Fuint 32))) store_checker_data_decl_1481).
Proof. vm_compute. reflexivity. Qed.
Lemma store_checker_data_split_1481 : store_checker_data_decl_1481 = statement_append store_checker_data_mid_1481 (@Qcons VarOrder.T (@Sfcnct VarOrder.T (@Eid VarOrder.T 1481) (@Eref VarOrder.T (@Eid VarOrder.T 8205))) store_checker_data_tail_1481).
Proof. vm_compute. reflexivity. Qed.
Lemma store_checker_data_straight_1481 : straight_statements store_checker_data_mid_1481.
Proof. vm_compute. exact I. Qed.
Lemma store_checker_data_mid_safe_1481 : formal_typed_suffix_safe flat_memories 1481 store_checker_data_mid_1481.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma store_checker_data_tail_safe_1481 : formal_typed_suffix_safe flat_memories 1481 store_checker_data_tail_1481.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma store_checker_data_nonregister_1481 : has_register 1481 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem store_checker_data_connection_1481 invalid old current result source_value value :
 VM.find 8205 old = Some source_value ->
 adapt_hvalue_as_type source_value (Gtyp (Fuint 32)) = Some value ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 1481 result = Some value.
Proof.
 intros Source Adapt Step.
 exact (declared_connection_value 1560 flat_statements store_checker_data_decl_1481 store_checker_data_mid_1481 store_checker_data_tail_1481
 1481 8205 32 source_value value invalid flat_memories old current result
 store_checker_data_position_1481 store_checker_data_split_1481 store_checker_data_straight_1481 store_checker_data_mid_safe_1481 store_checker_data_tail_safe_1481
 store_checker_data_nonregister_1481 (Logic.eq_refl _) Source Adapt Step).
Qed.
