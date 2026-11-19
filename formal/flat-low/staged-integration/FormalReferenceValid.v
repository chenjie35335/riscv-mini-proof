Require Import FormalDeclaredConnection ScalarNodeFrames FormalStatementSegments FormalTypedNodeFrames FormalTypedNodeEquation CoreSocModel ComparisonNodes RegisterInvariants.
From Coq Require Import ZArith.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory FormalInitialization.
Local Open Scope N_scope.
Definition reference_valid_decl_1517 := match straight_drop 1597 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition reference_valid_tail_1517 := match straight_drop 8221 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition reference_valid_mid_1517 := take_statements 6623 reference_valid_decl_1517.
Lemma reference_valid_position_1517 : straight_drop 1596 flat_statements = Some (@Qcons VarOrder.T (@Swire VarOrder.T 1517 (Gtyp (Fuint 1))) reference_valid_decl_1517).
Proof. vm_compute. reflexivity. Qed.
Lemma reference_valid_split_1517 : reference_valid_decl_1517 = statement_append reference_valid_mid_1517 (@Qcons VarOrder.T (@Sfcnct VarOrder.T (@Eid VarOrder.T 1517) (@Eref VarOrder.T (@Eid VarOrder.T 1395))) reference_valid_tail_1517).
Proof. vm_compute. reflexivity. Qed.
Lemma reference_valid_straight_1517 : straight_statements reference_valid_mid_1517.
Proof. vm_compute. exact I. Qed.
Lemma reference_valid_mid_safe_1517 : formal_typed_suffix_safe flat_memories 1517 reference_valid_mid_1517.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma reference_valid_tail_safe_1517 : formal_typed_suffix_safe flat_memories 1517 reference_valid_tail_1517.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma reference_valid_nonregister_1517 : has_register 1517 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem reference_valid_connection_1517 invalid old current result source_value value :
 VM.find 1395 old = Some source_value ->
 adapt_hvalue_as_type source_value (Gtyp (Fuint 1)) = Some value ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 1517 result = Some value.
Proof.
 intros Source Adapt Step.
 exact (declared_connection_value 1596 flat_statements reference_valid_decl_1517 reference_valid_mid_1517 reference_valid_tail_1517
 1517 1395 1 source_value value invalid flat_memories old current result
 reference_valid_position_1517 reference_valid_split_1517 reference_valid_straight_1517 reference_valid_mid_safe_1517 reference_valid_tail_safe_1517
 reference_valid_nonregister_1517 (Logic.eq_refl _) Source Adapt Step).
Qed.
Definition reference_valid_decl_1707 := match straight_drop 1787 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition reference_valid_tail_1707 := match straight_drop 7963 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition reference_valid_mid_1707 := take_statements 6175 reference_valid_decl_1707.
Lemma reference_valid_position_1707 : straight_drop 1786 flat_statements = Some (@Qcons VarOrder.T (@Swire VarOrder.T 1707 (Gtyp (Fuint 1))) reference_valid_decl_1707).
Proof. vm_compute. reflexivity. Qed.
Lemma reference_valid_split_1707 : reference_valid_decl_1707 = statement_append reference_valid_mid_1707 (@Qcons VarOrder.T (@Sfcnct VarOrder.T (@Eid VarOrder.T 1707) (@Eref VarOrder.T (@Eid VarOrder.T 1517))) reference_valid_tail_1707).
Proof. vm_compute. reflexivity. Qed.
Lemma reference_valid_straight_1707 : straight_statements reference_valid_mid_1707.
Proof. vm_compute. exact I. Qed.
Lemma reference_valid_mid_safe_1707 : formal_typed_suffix_safe flat_memories 1707 reference_valid_mid_1707.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma reference_valid_tail_safe_1707 : formal_typed_suffix_safe flat_memories 1707 reference_valid_tail_1707.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma reference_valid_nonregister_1707 : has_register 1707 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem reference_valid_connection_1707 invalid old current result source_value value :
 VM.find 1517 old = Some source_value ->
 adapt_hvalue_as_type source_value (Gtyp (Fuint 1)) = Some value ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 1707 result = Some value.
Proof.
 intros Source Adapt Step.
 exact (declared_connection_value 1786 flat_statements reference_valid_decl_1707 reference_valid_mid_1707 reference_valid_tail_1707
 1707 1517 1 source_value value invalid flat_memories old current result
 reference_valid_position_1707 reference_valid_split_1707 reference_valid_straight_1707 reference_valid_mid_safe_1707 reference_valid_tail_safe_1707
 reference_valid_nonregister_1707 (Logic.eq_refl _) Source Adapt Step).
Qed.
Theorem reference_valid_after_two invalid s0 s1 s2 b :
 VM.find 1395 s0 = Some (Gval (Fuint 1) [::b]) ->
 formal_value_iter invalid flat_memories s0 false s0 flat_statements = Some s1 ->
 formal_value_iter invalid flat_memories s1 false s1 flat_statements = Some s2 ->
 VM.find 1707 s2 = Some (Gval (Fuint 1) [::b]).
Proof.
 intros Valid S1 S2.
 assert (Middle : VM.find 1517 s1 = Some (Gval (Fuint 1) [::b])).
 { eapply reference_valid_connection_1517; [exact Valid|destruct b; reflexivity|exact S1]. }
 eapply reference_valid_connection_1707; [exact Middle|destruct b; reflexivity|exact S2].
Qed.
Print Assumptions reference_valid_after_two.
