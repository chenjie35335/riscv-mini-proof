Require Import FormalDeclaredUnaryConnection.
Require Import FormalDeclaredConnection ScalarNodeFrames FormalStatementSegments FormalTypedNodeFrames FormalTypedNodeEquation CoreSocModel ComparisonNodes RegisterInvariants.
From Coq Require Import ZArith.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From firrtl Require Import Firrtl_with_implicit_widths Env_with_implicit_widths HiEnv_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory FormalInitialization.
Local Open Scope N_scope.
Definition store_request_data_decl_79 := match straight_drop 57 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition store_request_data_tail_79 := match straight_drop 8763 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition store_request_data_mid_79 := take_statements 8705 store_request_data_decl_79.
Lemma store_request_data_position_79 : straight_drop 56 flat_statements = Some (@Qcons VarOrder.T (@Swire VarOrder.T 79 (Gtyp (Fuint 32))) store_request_data_decl_79).
Proof. vm_compute. reflexivity. Qed.
Lemma store_request_data_split_79 : store_request_data_decl_79 = statement_append store_request_data_mid_79 (@Qcons VarOrder.T (@Sfcnct VarOrder.T (@Eid VarOrder.T 79) (@Eprim_unop VarOrder.T (Uextr 31 0) (@Eref VarOrder.T (@Eid VarOrder.T 7837)))) store_request_data_tail_79).
Proof. vm_compute. reflexivity. Qed.
Lemma store_request_data_straight_79 : straight_statements store_request_data_mid_79.
Proof. vm_compute. exact I. Qed.
Lemma store_request_data_mid_safe_79 : formal_typed_suffix_safe flat_memories 79 store_request_data_mid_79.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma store_request_data_tail_safe_79 : formal_typed_suffix_safe flat_memories 79 store_request_data_tail_79.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma store_request_data_nonregister_79 : has_register 79 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem store_request_data_connection_79 invalid old current result source_value value :
 eval_hfexpr_with_memory flat_memories (@Eprim_unop VarOrder.T (Uextr 31 0) (@Eref VarOrder.T (@Eid VarOrder.T 7837))) old old = Some source_value ->
 adapt_hvalue_as_type source_value (Gtyp (Fuint 32)) = Some value ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 79 result = Some value.
Proof.
 intros Source Adapt Step.
 exact (declared_unary_connection_value 56 flat_statements store_request_data_decl_79 store_request_data_mid_79 store_request_data_tail_79
 79 7837 (Uextr 31 0) 32 source_value value invalid flat_memories old current result
 store_request_data_position_79 store_request_data_split_79 store_request_data_straight_79 store_request_data_mid_safe_79 store_request_data_tail_safe_79
 store_request_data_nonregister_79 (Logic.eq_refl _) Source Adapt Step).
Qed.

