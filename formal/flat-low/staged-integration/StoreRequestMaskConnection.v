Require Import FormalDeclaredUnaryConnection.
Require Import FormalDeclaredConnection ScalarNodeFrames FormalStatementSegments FormalTypedNodeFrames FormalTypedNodeEquation CoreSocModel ComparisonNodes RegisterInvariants.
From Coq Require Import ZArith.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From firrtl Require Import Firrtl_with_implicit_widths Env_with_implicit_widths HiEnv_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory FormalInitialization.
Local Open Scope N_scope.
Definition store_request_mask_decl_80 := match straight_drop 58 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition store_request_mask_tail_80 := match straight_drop 8764 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition store_request_mask_mid_80 := take_statements 8705 store_request_mask_decl_80.
Lemma store_request_mask_position_80 : straight_drop 57 flat_statements = Some (@Qcons VarOrder.T (@Swire VarOrder.T 80 (Gtyp (Fuint 4))) store_request_mask_decl_80).
Proof. vm_compute. reflexivity. Qed.
Lemma store_request_mask_split_80 : store_request_mask_decl_80 = statement_append store_request_mask_mid_80 (@Qcons VarOrder.T (@Sfcnct VarOrder.T (@Eid VarOrder.T 80) (@Eprim_unop VarOrder.T (Uextr 3 0) (@Eref VarOrder.T (@Eid VarOrder.T 7848)))) store_request_mask_tail_80).
Proof. vm_compute. reflexivity. Qed.
Lemma store_request_mask_straight_80 : straight_statements store_request_mask_mid_80.
Proof. vm_compute. exact I. Qed.
Lemma store_request_mask_mid_safe_80 : formal_typed_suffix_safe flat_memories 80 store_request_mask_mid_80.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma store_request_mask_tail_safe_80 : formal_typed_suffix_safe flat_memories 80 store_request_mask_tail_80.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma store_request_mask_nonregister_80 : has_register 80 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem store_request_mask_connection_80 invalid old current result source_value value :
 eval_hfexpr_with_memory flat_memories (@Eprim_unop VarOrder.T (Uextr 3 0) (@Eref VarOrder.T (@Eid VarOrder.T 7848))) old old = Some source_value ->
 adapt_hvalue_as_type source_value (Gtyp (Fuint 4)) = Some value ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 80 result = Some value.
Proof.
 intros Source Adapt Step.
 exact (declared_unary_connection_value 57 flat_statements store_request_mask_decl_80 store_request_mask_mid_80 store_request_mask_tail_80
 80 7848 (Uextr 3 0) 4 source_value value invalid flat_memories old current result
 store_request_mask_position_80 store_request_mask_split_80 store_request_mask_straight_80 store_request_mask_mid_safe_80 store_request_mask_tail_safe_80
 store_request_mask_nonregister_80 (Logic.eq_refl _) Source Adapt Step).
Qed.

