Require Import FormalDeclaredConnection ScalarNodeFrames FormalStatementSegments FormalTypedNodeFrames FormalTypedNodeEquation CoreSocModel ComparisonNodes RegisterInvariants.
From Coq Require Import ZArith.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory FormalInitialization.
Local Open Scope N_scope.
Definition reference_output_decl_1787 := match straight_drop 1867 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition reference_output_tail_1787 := match straight_drop 7358 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition reference_output_mid_1787 := take_statements 5490 reference_output_decl_1787.
Lemma reference_output_position_1787 : straight_drop 1866 flat_statements = Some (@Qcons VarOrder.T (@Swire VarOrder.T 1787 (Gtyp (Fuint 32))) reference_output_decl_1787).
Proof. vm_compute. reflexivity. Qed.
Lemma reference_output_split_1787 : reference_output_decl_1787 = statement_append reference_output_mid_1787 (@Qcons VarOrder.T (@Sfcnct VarOrder.T (@Eid VarOrder.T 1787) (@Eref VarOrder.T (@Eid VarOrder.T 3256))) reference_output_tail_1787).
Proof. vm_compute. reflexivity. Qed.
Lemma reference_output_straight_1787 : straight_statements reference_output_mid_1787.
Proof. vm_compute. exact I. Qed.
Lemma reference_output_mid_safe_1787 : formal_typed_suffix_safe flat_memories 1787 reference_output_mid_1787.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma reference_output_tail_safe_1787 : formal_typed_suffix_safe flat_memories 1787 reference_output_tail_1787.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma reference_output_nonregister_1787 : has_register 1787 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem reference_output_connection_1787 invalid old current result source_value value :
 VM.find 3256 old = Some source_value ->
 adapt_hvalue_as_type source_value (Gtyp (Fuint 32)) = Some value ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 1787 result = Some value.
Proof.
 intros Source Adapt Step.
 exact (declared_connection_value 1866 flat_statements reference_output_decl_1787 reference_output_mid_1787 reference_output_tail_1787
 1787 3256 32 source_value value invalid flat_memories old current result
 reference_output_position_1787 reference_output_split_1787 reference_output_straight_1787 reference_output_mid_safe_1787 reference_output_tail_safe_1787
 reference_output_nonregister_1787 (Logic.eq_refl _) Source Adapt Step).
Qed.
Definition reference_output_decl_1597 := match straight_drop 1677 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition reference_output_tail_1597 := match straight_drop 7815 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition reference_output_mid_1597 := take_statements 6137 reference_output_decl_1597.
Lemma reference_output_position_1597 : straight_drop 1676 flat_statements = Some (@Qcons VarOrder.T (@Swire VarOrder.T 1597 (Gtyp (Fuint 32))) reference_output_decl_1597).
Proof. vm_compute. reflexivity. Qed.
Lemma reference_output_split_1597 : reference_output_decl_1597 = statement_append reference_output_mid_1597 (@Qcons VarOrder.T (@Sfcnct VarOrder.T (@Eid VarOrder.T 1597) (@Eref VarOrder.T (@Eid VarOrder.T 1787))) reference_output_tail_1597).
Proof. vm_compute. reflexivity. Qed.
Lemma reference_output_straight_1597 : straight_statements reference_output_mid_1597.
Proof. vm_compute. exact I. Qed.
Lemma reference_output_mid_safe_1597 : formal_typed_suffix_safe flat_memories 1597 reference_output_mid_1597.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma reference_output_tail_safe_1597 : formal_typed_suffix_safe flat_memories 1597 reference_output_tail_1597.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma reference_output_nonregister_1597 : has_register 1597 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem reference_output_connection_1597 invalid old current result source_value value :
 VM.find 1787 old = Some source_value ->
 adapt_hvalue_as_type source_value (Gtyp (Fuint 32)) = Some value ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 1597 result = Some value.
Proof.
 intros Source Adapt Step.
 exact (declared_connection_value 1676 flat_statements reference_output_decl_1597 reference_output_mid_1597 reference_output_tail_1597
 1597 1787 32 source_value value invalid flat_memories old current result
 reference_output_position_1597 reference_output_split_1597 reference_output_straight_1597 reference_output_mid_safe_1597 reference_output_tail_safe_1597
 reference_output_nonregister_1597 (Logic.eq_refl _) Source Adapt Step).
Qed.
Print Assumptions reference_output_connection_1597.
