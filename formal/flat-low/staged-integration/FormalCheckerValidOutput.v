Require Import RegisterInvariants CoreSocModel ComparisonNodes ScalarNodeFrames FormalTypedNodeFrames FormalTypedNodeEquation.
From Coq Require Import ZArith.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths Firrtl_with_implicit_widths HiEnv_with_implicit_widths
 HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Require Import FormalDeclaredConnection FormalStatementSegments NormalizedBit SymbolicBit.
Definition valid_expr_7956 := (@Eref VarOrder.T (@Eid VarOrder.T 7952)).
Definition valid_tail_7956 := match straight_drop 8463 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma valid_position_7956 : straight_drop 8462 flat_statements = Some (@Qcons VarOrder.T (@Snode VarOrder.T 7956 valid_expr_7956) valid_tail_7956).
Proof. vm_compute. reflexivity. Qed.
Lemma valid_suffix_7956 : formal_typed_suffix_safe flat_memories 7956 valid_tail_7956.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma valid_nonregister_7956 : has_register 7956 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem valid_node_7956 invalid old current result value :
 eval_hfexpr_with_memory flat_memories valid_expr_7956 old old = Some value ->
 type_of_val value = Gtyp (Fuint 1) ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 7956 result = Some value.
Proof. intros Eval Typed Step. eapply formal_combinational_known_node;
 [exact valid_position_7956|exact valid_suffix_7956|exact valid_nonregister_7956|exact Eval|exact Typed|exact Step]. Qed.
Definition checker_output_decl_1395 := match straight_drop 1475 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition checker_output_tail_1395 := match straight_drop 8884 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition checker_output_mid_1395 := take_statements 7408 checker_output_decl_1395.
Lemma checker_output_position_1395 : straight_drop 1474 flat_statements = Some (@Qcons VarOrder.T (@Swire VarOrder.T 1395 (Gtyp (Fuint 1))) checker_output_decl_1395).
Proof. vm_compute. reflexivity. Qed.
Lemma checker_output_split_1395 : checker_output_decl_1395 = statement_append checker_output_mid_1395 (@Qcons VarOrder.T (@Sfcnct VarOrder.T (@Eid VarOrder.T 1395) (@Eref VarOrder.T (@Eid VarOrder.T 7956))) checker_output_tail_1395).
Proof. vm_compute. reflexivity. Qed.
Lemma checker_output_straight_1395 : straight_statements checker_output_mid_1395.
Proof. vm_compute. exact I. Qed.
Lemma checker_output_mid_safe_1395 : formal_typed_suffix_safe flat_memories 1395 checker_output_mid_1395.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma checker_output_tail_safe_1395 : formal_typed_suffix_safe flat_memories 1395 checker_output_tail_1395.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma checker_output_nonregister_1395 : has_register 1395 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem checker_output_connection_1395 invalid old current result source_value value :
 VM.find 7956 old = Some source_value ->
 adapt_hvalue_as_type source_value (Gtyp (Fuint 1)) = Some value ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 1395 result = Some value.
Proof.
 intros Source Adapt Step.
 exact (declared_connection_value 1474 flat_statements checker_output_decl_1395 checker_output_mid_1395 checker_output_tail_1395
 1395 7956 1 source_value value invalid flat_memories old current result
 checker_output_position_1395 checker_output_split_1395 checker_output_straight_1395 checker_output_mid_safe_1395 checker_output_tail_safe_1395
 checker_output_nonregister_1395 (Logic.eq_refl _) Source Adapt Step).
Qed.
Theorem checker_output_after_two invalid s0 s1 s2 value :
 normalized_bit value -> VM.find 7952 s0 = Some value ->
 formal_value_iter invalid flat_memories s0 false s0 flat_statements = Some s1 ->
 formal_value_iter invalid flat_memories s1 false s1 flat_statements = Some s2 ->
 VM.find 1395 s2 = Some value.
Proof.
 intros Normal Value S1 S2.
 assert (Middle : VM.find 7956 s1 = Some value).
 { eapply valid_node_7956; [|exact (normalized_bit_type value Normal)|exact S1].
   cbn [valid_expr_7956 eval_hfexpr_with_memory eval_href_with_memory]. exact Value. }
 eapply checker_output_connection_1395;
 [exact Middle|exact (normalized_bit_adapt value Normal)|exact S2].
Qed.
Print Assumptions checker_output_after_two.
