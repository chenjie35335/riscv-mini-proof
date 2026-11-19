Require Import FormalDeclaredConnection ScalarNodeFrames FormalStatementSegments FormalTypedNodeFrames FormalTypedNodeEquation CoreSocModel ComparisonNodes RegisterInvariants.
From Coq Require Import ZArith.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory FormalInitialization.
Local Open Scope N_scope.
Definition rf_reset_decl_788 := match straight_drop 798 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition rf_reset_tail_788 := match straight_drop 8806 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition rf_reset_mid_788 := take_statements 8007 rf_reset_decl_788.
Lemma rf_reset_position_788 : straight_drop 797 flat_statements = Some (@Qcons VarOrder.T (@Swire VarOrder.T 788 (Gtyp (Fuint 32))) rf_reset_decl_788).
Proof. vm_compute. reflexivity. Qed.
Lemma rf_reset_split_788 : rf_reset_decl_788 = statement_append rf_reset_mid_788 (@Qcons VarOrder.T (@Sfcnct VarOrder.T (@Eid VarOrder.T 788) (@Eref VarOrder.T (@Eid VarOrder.T 8092))) rf_reset_tail_788).
Proof. vm_compute. reflexivity. Qed.
Lemma rf_reset_straight_788 : straight_statements rf_reset_mid_788.
Proof. vm_compute. exact I. Qed.
Lemma rf_reset_mid_safe_788 : formal_typed_suffix_safe flat_memories 788 rf_reset_mid_788.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma rf_reset_tail_safe_788 : formal_typed_suffix_safe flat_memories 788 rf_reset_tail_788.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma rf_reset_nonregister_788 : has_register 788 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem rf_reset_connection_788 invalid old current result source_value value :
 VM.find 8092 old = Some source_value ->
 adapt_hvalue_as_type source_value (Gtyp (Fuint 32)) = Some value ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 788 result = Some value.
Proof.
 intros Source Adapt Step.
 exact (declared_connection_value 797 flat_statements rf_reset_decl_788 rf_reset_mid_788 rf_reset_tail_788
 788 8092 32 source_value value invalid flat_memories old current result
 rf_reset_position_788 rf_reset_split_788 rf_reset_straight_788 rf_reset_mid_safe_788 rf_reset_tail_safe_788
 rf_reset_nonregister_788 (Logic.eq_refl _) Source Adapt Step).
Qed.
Definition rf_reset_decl_779 := match straight_drop 789 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition rf_reset_tail_779 := match straight_drop 8799 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition rf_reset_mid_779 := take_statements 8009 rf_reset_decl_779.
Lemma rf_reset_position_779 : straight_drop 788 flat_statements = Some (@Qcons VarOrder.T (@Swire VarOrder.T 779 (Gtyp (Fuint 1))) rf_reset_decl_779).
Proof. vm_compute. reflexivity. Qed.
Lemma rf_reset_split_779 : rf_reset_decl_779 = statement_append rf_reset_mid_779 (@Qcons VarOrder.T (@Sfcnct VarOrder.T (@Eid VarOrder.T 779) (@Eref VarOrder.T (@Eid VarOrder.T 65))) rf_reset_tail_779).
Proof. vm_compute. reflexivity. Qed.
Lemma rf_reset_straight_779 : straight_statements rf_reset_mid_779.
Proof. vm_compute. exact I. Qed.
Lemma rf_reset_mid_safe_779 : formal_typed_suffix_safe flat_memories 779 rf_reset_mid_779.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma rf_reset_tail_safe_779 : formal_typed_suffix_safe flat_memories 779 rf_reset_tail_779.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma rf_reset_nonregister_779 : has_register 779 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem rf_reset_connection_779 invalid old current result source_value value :
 VM.find 65 old = Some source_value ->
 adapt_hvalue_as_type source_value (Gtyp (Fuint 1)) = Some value ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 779 result = Some value.
Proof.
 intros Source Adapt Step.
 exact (declared_connection_value 788 flat_statements rf_reset_decl_779 rf_reset_mid_779 rf_reset_tail_779
 779 65 1 source_value value invalid flat_memories old current result
 rf_reset_position_779 rf_reset_split_779 rf_reset_straight_779 rf_reset_mid_safe_779 rf_reset_tail_safe_779
 rf_reset_nonregister_779 (Logic.eq_refl _) Source Adapt Step).
Qed.
Print Assumptions rf_reset_connection_779.
