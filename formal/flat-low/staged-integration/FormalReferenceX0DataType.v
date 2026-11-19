Require Import FormalDeclaredConnection ScalarNodeFrames FormalStatementSegments FormalTypedNodeFrames FormalTypedNodeEquation CoreSocModel ComparisonNodes RegisterInvariants.
From Coq Require Import ZArith.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory FormalInitialization.
Local Open Scope N_scope.
Definition reference_data_decl_1717 := match straight_drop 1797 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition reference_data_tail_1717 := match straight_drop 7965 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition reference_data_mid_1717 := take_statements 6167 reference_data_decl_1717.
Lemma reference_data_position_1717 : straight_drop 1796 flat_statements = Some (@Qcons VarOrder.T (@Swire VarOrder.T 1717 (Gtyp (Fuint 32))) reference_data_decl_1717).
Proof. vm_compute. reflexivity. Qed.
Lemma reference_data_split_1717 : reference_data_decl_1717 = statement_append reference_data_mid_1717 (@Qcons VarOrder.T (@Sfcnct VarOrder.T (@Eid VarOrder.T 1717) (@Eref VarOrder.T (@Eid VarOrder.T 7299))) reference_data_tail_1717).
Proof. vm_compute. reflexivity. Qed.
Lemma reference_data_straight_1717 : straight_statements reference_data_mid_1717.
Proof. vm_compute. exact I. Qed.
Lemma reference_data_mid_safe_1717 : formal_typed_suffix_safe flat_memories 1717 reference_data_mid_1717.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma reference_data_tail_safe_1717 : formal_typed_suffix_safe flat_memories 1717 reference_data_tail_1717.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma reference_data_nonregister_1717 : has_register 1717 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem reference_data_connection_1717 invalid old current result source_value value :
 VM.find 7299 old = Some source_value ->
 adapt_hvalue_as_type source_value (Gtyp (Fuint 32)) = Some value ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 1717 result = Some value.
Proof.
 intros Source Adapt Step.
 exact (declared_connection_value 1796 flat_statements reference_data_decl_1717 reference_data_mid_1717 reference_data_tail_1717
 1717 7299 32 source_value value invalid flat_memories old current result
 reference_data_position_1717 reference_data_split_1717 reference_data_straight_1717 reference_data_mid_safe_1717 reference_data_tail_safe_1717
 reference_data_nonregister_1717 (Logic.eq_refl _) Source Adapt Step).
Qed.
Require Import FormalDeclaredConnectionObservation ScalarSinkTypes.
Theorem reference_data_type invalid old current result :
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 exists value, VM.find 1717 result = Some value /\ type_of_val value = Gtyp (Fuint 32).
Proof.
 intro Step.
 destruct (declared_connection_observation 1796 flat_statements reference_data_decl_1717 reference_data_mid_1717 reference_data_tail_1717
 1717 7299 32 invalid flat_memories old current result
 reference_data_position_1717 reference_data_split_1717 reference_data_straight_1717 reference_data_mid_safe_1717 reference_data_tail_safe_1717
 reference_data_nonregister_1717 (Logic.eq_refl _) Step) as [source [value [Source [Adapt Value]]]].
 exists value. split; [exact Value|eapply adapted_uint_result_type; exact Adapt].
Qed.
Definition reference_data_expr_2177 := (@Eref VarOrder.T (@Eid VarOrder.T 1717)).
Definition reference_data_tail_2177 := match straight_drop 2257 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma reference_data_position_2177 : straight_drop 2256 flat_statements = Some (@Qcons VarOrder.T (@Snode VarOrder.T 2177 reference_data_expr_2177) reference_data_tail_2177).
Proof. vm_compute. reflexivity. Qed.
Lemma reference_data_suffix_2177 : formal_typed_suffix_safe flat_memories 2177 reference_data_tail_2177.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma reference_data_nonregister_2177 : has_register 2177 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem reference_data_node_2177 invalid old current result value :
 eval_hfexpr_with_memory flat_memories reference_data_expr_2177 old old = Some value ->
 type_of_val value = Gtyp (Fuint 32) ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 2177 result = Some value.
Proof. intros Eval Typed Step. eapply formal_combinational_known_node;
 [exact reference_data_position_2177|exact reference_data_suffix_2177|exact reference_data_nonregister_2177|exact Eval|exact Typed|exact Step]. Qed.
Theorem reference_x0_data_type_after_two invalid s0 s1 s2 :
 formal_value_iter invalid flat_memories s0 false s0 flat_statements = Some s1 ->
 formal_value_iter invalid flat_memories s1 false s1 flat_statements = Some s2 ->
 exists value, VM.find 2177 s2 = Some value /\ type_of_val value = Gtyp (Fuint 32).
Proof.
 intros S1 S2.
 destruct (reference_data_type invalid s0 s0 s1 S1) as [value [Value Typed]].
 exists value. split; [|exact Typed].
 eapply reference_data_node_2177; [|exact Typed|exact S2].
 cbn [reference_data_expr_2177 eval_hfexpr_with_memory eval_href_with_memory]. exact Value.
Qed.
Print Assumptions reference_x0_data_type_after_two.
