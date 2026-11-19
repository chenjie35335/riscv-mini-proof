Require Import CoreSocModel ComparisonNodes RegisterInvariants ScalarNodeFrames FormalTypedNodeFrames FormalTypedNodeEquation.
From Coq Require Import ZArith.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From firrtl Require Import Firrtl_with_implicit_widths Env_with_implicit_widths HiEnv_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Definition exception_selection_1883_expr : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 1707)) (@Eref VarOrder.T (@Eid VarOrder.T 1706)) (@Econst VarOrder.T (Fuint 1) [::false])).
Definition exception_selection_1883_tail := match straight_drop 1963 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma exception_selection_1883_position : straight_drop 1962 flat_statements = Some (@Qcons VarOrder.T (@Snode VarOrder.T 1883 exception_selection_1883_expr) exception_selection_1883_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma exception_selection_1883_safe : formal_typed_suffix_safe flat_memories 1883 exception_selection_1883_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma exception_selection_1883_nonregister : has_register 1883 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem exception_selection_1883_value invalid old current result bits :
 eval_hfexpr_with_memory flat_memories exception_selection_1883_expr old old = Some (Gval (Fuint 32) bits) ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 1883 result = Some (Gval (Fuint 32) bits).
Proof.
 intros Eval Step. eapply formal_combinational_known_node;
 [exact exception_selection_1883_position|exact exception_selection_1883_safe|exact exception_selection_1883_nonregister|exact Eval|reflexivity|exact Step].
Qed.
Definition exception_selection_6811_expr : hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Uextr 31 0) (@Eref VarOrder.T (@Eid VarOrder.T 1884))).
Definition exception_selection_6811_tail := match straight_drop 6891 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma exception_selection_6811_position : straight_drop 6890 flat_statements = Some (@Qcons VarOrder.T (@Snode VarOrder.T 6811 exception_selection_6811_expr) exception_selection_6811_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma exception_selection_6811_safe : formal_typed_suffix_safe flat_memories 6811 exception_selection_6811_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma exception_selection_6811_nonregister : has_register 6811 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem exception_selection_6811_value invalid old current result bits :
 eval_hfexpr_with_memory flat_memories exception_selection_6811_expr old old = Some (Gval (Fuint 32) bits) ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 6811 result = Some (Gval (Fuint 32) bits).
Proof.
 intros Eval Step. eapply formal_combinational_known_node;
 [exact exception_selection_6811_position|exact exception_selection_6811_safe|exact exception_selection_6811_nonregister|exact Eval|reflexivity|exact Step].
Qed.
Definition exception_selection_7088_expr : hfexpr VarOrder.T := (@Econst VarOrder.T (Fuint 32) [::false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false]).
Definition exception_selection_7088_tail := match straight_drop 7168 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma exception_selection_7088_position : straight_drop 7167 flat_statements = Some (@Qcons VarOrder.T (@Snode VarOrder.T 7088 exception_selection_7088_expr) exception_selection_7088_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma exception_selection_7088_safe : formal_typed_suffix_safe flat_memories 7088 exception_selection_7088_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma exception_selection_7088_nonregister : has_register 7088 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem exception_selection_7088_value invalid old current result bits :
 eval_hfexpr_with_memory flat_memories exception_selection_7088_expr old old = Some (Gval (Fuint 32) bits) ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 7088 result = Some (Gval (Fuint 32) bits).
Proof.
 intros Eval Step. eapply formal_combinational_known_node;
 [exact exception_selection_7088_position|exact exception_selection_7088_safe|exact exception_selection_7088_nonregister|exact Eval|reflexivity|exact Step].
Qed.
Definition exception_selection_7089_expr : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 6780)) (@Eref VarOrder.T (@Eid VarOrder.T 6811)) (@Eref VarOrder.T (@Eid VarOrder.T 7088))).
Definition exception_selection_7089_tail := match straight_drop 7169 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma exception_selection_7089_position : straight_drop 7168 flat_statements = Some (@Qcons VarOrder.T (@Snode VarOrder.T 7089 exception_selection_7089_expr) exception_selection_7089_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma exception_selection_7089_safe : formal_typed_suffix_safe flat_memories 7089 exception_selection_7089_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma exception_selection_7089_nonregister : has_register 7089 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem exception_selection_7089_value invalid old current result bits :
 eval_hfexpr_with_memory flat_memories exception_selection_7089_expr old old = Some (Gval (Fuint 32) bits) ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 7089 result = Some (Gval (Fuint 32) bits).
Proof.
 intros Eval Step. eapply formal_combinational_known_node;
 [exact exception_selection_7089_position|exact exception_selection_7089_safe|exact exception_selection_7089_nonregister|exact Eval|reflexivity|exact Step].
Qed.
Definition exception_selection_7120_expr : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 1707)) (@Eref VarOrder.T (@Eid VarOrder.T 7089)) (@Eref VarOrder.T (@Eid VarOrder.T 7088))).
Definition exception_selection_7120_tail := match straight_drop 7200 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma exception_selection_7120_position : straight_drop 7199 flat_statements = Some (@Qcons VarOrder.T (@Snode VarOrder.T 7120 exception_selection_7120_expr) exception_selection_7120_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma exception_selection_7120_safe : formal_typed_suffix_safe flat_memories 7120 exception_selection_7120_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma exception_selection_7120_nonregister : has_register 7120 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem exception_selection_7120_value invalid old current result bits :
 eval_hfexpr_with_memory flat_memories exception_selection_7120_expr old old = Some (Gval (Fuint 32) bits) ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 7120 result = Some (Gval (Fuint 32) bits).
Proof.
 intros Eval Step. eapply formal_combinational_known_node;
 [exact exception_selection_7120_position|exact exception_selection_7120_safe|exact exception_selection_7120_nonregister|exact Eval|reflexivity|exact Step].
Qed.
Print Assumptions exception_selection_7120_value.
