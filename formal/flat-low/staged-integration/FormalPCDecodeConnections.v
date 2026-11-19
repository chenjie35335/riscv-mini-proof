Require Import FormalDeclaredConnection ScalarNodeFrames FormalStatementSegments FormalTypedNodeFrames FormalTypedNodeEquation CoreSocModel ComparisonNodes RegisterInvariants.
From Coq Require Import ZArith.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory FormalInitialization.
Local Open Scope N_scope.
Definition pc_decode_decl_8250 := match straight_drop 9011 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition pc_decode_tail_8250 := match straight_drop 9761 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition pc_decode_mid_8250 := take_statements 749 pc_decode_decl_8250.
Lemma pc_decode_position_8250 : straight_drop 9010 flat_statements = Some (@Qcons VarOrder.T (@Swire VarOrder.T 8250 (Gtyp (Fuint 2))) pc_decode_decl_8250).
Proof. vm_compute. reflexivity. Qed.
Lemma pc_decode_split_8250 : pc_decode_decl_8250 = statement_append pc_decode_mid_8250 (@Qcons VarOrder.T (@Sfcnct VarOrder.T (@Eid VarOrder.T 8250) (@Eref VarOrder.T (@Eid VarOrder.T 8409))) pc_decode_tail_8250).
Proof. vm_compute. reflexivity. Qed.
Lemma pc_decode_straight_8250 : straight_statements pc_decode_mid_8250.
Proof. vm_compute. exact I. Qed.
Lemma pc_decode_mid_safe_8250 : formal_typed_suffix_safe flat_memories 8250 pc_decode_mid_8250.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma pc_decode_tail_safe_8250 : formal_typed_suffix_safe flat_memories 8250 pc_decode_tail_8250.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma pc_decode_nonregister_8250 : has_register 8250 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem pc_decode_connection_8250 invalid old current result source_value value :
 VM.find 8409 old = Some source_value ->
 adapt_hvalue_as_type source_value (Gtyp (Fuint 2)) = Some value ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 8250 result = Some value.
Proof.
 intros Source Adapt Step.
 exact (declared_connection_value 9010 flat_statements pc_decode_decl_8250 pc_decode_mid_8250 pc_decode_tail_8250
 8250 8409 2 source_value value invalid flat_memories old current result
 pc_decode_position_8250 pc_decode_split_8250 pc_decode_straight_8250 pc_decode_mid_safe_8250 pc_decode_tail_safe_8250
 pc_decode_nonregister_8250 (Logic.eq_refl _) Source Adapt Step).
Qed.
Definition pc_decode_decl_84 := match straight_drop 62 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition pc_decode_tail_84 := match straight_drop 9991 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition pc_decode_mid_84 := take_statements 9928 pc_decode_decl_84.
Lemma pc_decode_position_84 : straight_drop 61 flat_statements = Some (@Qcons VarOrder.T (@Swire VarOrder.T 84 (Gtyp (Fuint 2))) pc_decode_decl_84).
Proof. vm_compute. reflexivity. Qed.
Lemma pc_decode_split_84 : pc_decode_decl_84 = statement_append pc_decode_mid_84 (@Qcons VarOrder.T (@Sfcnct VarOrder.T (@Eid VarOrder.T 84) (@Eref VarOrder.T (@Eid VarOrder.T 8250))) pc_decode_tail_84).
Proof. vm_compute. reflexivity. Qed.
Lemma pc_decode_straight_84 : straight_statements pc_decode_mid_84.
Proof. vm_compute. exact I. Qed.
Lemma pc_decode_mid_safe_84 : formal_typed_suffix_safe flat_memories 84 pc_decode_mid_84.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma pc_decode_tail_safe_84 : formal_typed_suffix_safe flat_memories 84 pc_decode_tail_84.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma pc_decode_nonregister_84 : has_register 84 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem pc_decode_connection_84 invalid old current result source_value value :
 VM.find 8250 old = Some source_value ->
 adapt_hvalue_as_type source_value (Gtyp (Fuint 2)) = Some value ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 84 result = Some value.
Proof.
 intros Source Adapt Step.
 exact (declared_connection_value 61 flat_statements pc_decode_decl_84 pc_decode_mid_84 pc_decode_tail_84
 84 8250 2 source_value value invalid flat_memories old current result
 pc_decode_position_84 pc_decode_split_84 pc_decode_straight_84 pc_decode_mid_safe_84 pc_decode_tail_safe_84
 pc_decode_nonregister_84 (Logic.eq_refl _) Source Adapt Step).
Qed.
Definition pc_decode_decl_1360 := match straight_drop 1439 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition pc_decode_tail_1360 := match straight_drop 1472 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition pc_decode_mid_1360 := take_statements 32 pc_decode_decl_1360.
Lemma pc_decode_position_1360 : straight_drop 1438 flat_statements = Some (@Qcons VarOrder.T (@Swire VarOrder.T 1360 (Gtyp (Fuint 1))) pc_decode_decl_1360).
Proof. vm_compute. reflexivity. Qed.
Lemma pc_decode_split_1360 : pc_decode_decl_1360 = statement_append pc_decode_mid_1360 (@Qcons VarOrder.T (@Sfcnct VarOrder.T (@Eid VarOrder.T 1360) (@Eref VarOrder.T (@Eid VarOrder.T 1392))) pc_decode_tail_1360).
Proof. vm_compute. reflexivity. Qed.
Lemma pc_decode_straight_1360 : straight_statements pc_decode_mid_1360.
Proof. vm_compute. exact I. Qed.
Lemma pc_decode_mid_safe_1360 : formal_typed_suffix_safe flat_memories 1360 pc_decode_mid_1360.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma pc_decode_tail_safe_1360 : formal_typed_suffix_safe flat_memories 1360 pc_decode_tail_1360.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma pc_decode_nonregister_1360 : has_register 1360 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem pc_decode_connection_1360 invalid old current result source_value value :
 VM.find 1392 old = Some source_value ->
 adapt_hvalue_as_type source_value (Gtyp (Fuint 1)) = Some value ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 1360 result = Some value.
Proof.
 intros Source Adapt Step.
 exact (declared_connection_value 1438 flat_statements pc_decode_decl_1360 pc_decode_mid_1360 pc_decode_tail_1360
 1360 1392 1 source_value value invalid flat_memories old current result
 pc_decode_position_1360 pc_decode_split_1360 pc_decode_straight_1360 pc_decode_mid_safe_1360 pc_decode_tail_safe_1360
 pc_decode_nonregister_1360 (Logic.eq_refl _) Source Adapt Step).
Qed.
Print Assumptions pc_decode_connection_84.
