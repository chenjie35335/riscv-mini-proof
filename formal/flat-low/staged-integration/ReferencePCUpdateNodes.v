Require Import CoreSocModel ComparisonNodes RegisterInvariants ScalarNodeFrames FormalTypedNodeFrames FormalTypedNodeEquation FormalSuccessfulNodeEvaluation.
From Coq Require Import ZArith.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From firrtl Require Import Firrtl_with_implicit_widths Env_with_implicit_widths HiEnv_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Definition reference_pc_update_7109_expr := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 1707)) (@Eref VarOrder.T (@Eid VarOrder.T 7094)) (@Eref VarOrder.T (@Eid VarOrder.T 2812))).
Definition reference_pc_update_7109_tail := match straight_drop 7189 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma reference_pc_update_7109_position : straight_drop 7188 flat_statements = Some (@Qcons VarOrder.T (@Snode VarOrder.T 7109 reference_pc_update_7109_expr) reference_pc_update_7109_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma reference_pc_update_7109_safe : formal_typed_suffix_safe flat_memories 7109 reference_pc_update_7109_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma reference_pc_update_7109_nonregister : has_register 7109 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem reference_pc_update_7109_value invalid old current result width bits :
 eval_hfexpr_with_memory flat_memories reference_pc_update_7109_expr old old = Some (Gval (Fuint width) bits) ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 7109 result = Some (Gval (Fuint width) bits).
Proof.
 intros Eval Step. eapply formal_combinational_known_node;
 [exact reference_pc_update_7109_position|exact reference_pc_update_7109_safe|exact reference_pc_update_7109_nonregister|exact Eval|reflexivity|exact Step].
Qed.
Theorem reference_pc_update_7109_evaluation invalid old current result :
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 exists value, eval_hfexpr_with_memory flat_memories reference_pc_update_7109_expr old old = Some value.
Proof.
 intro Step.
 exact (formal_successful_node_evaluation 7188 flat_statements reference_pc_update_7109_tail 7109 reference_pc_update_7109_expr invalid flat_memories old false current result reference_pc_update_7109_position Step).
Qed.
Definition reference_pc_update_7149_expr := (@Eprim_unop VarOrder.T (Uextr 31 0) (@Eref VarOrder.T (@Eid VarOrder.T 7109))).
Definition reference_pc_update_7149_tail := match straight_drop 7229 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma reference_pc_update_7149_position : straight_drop 7228 flat_statements = Some (@Qcons VarOrder.T (@Snode VarOrder.T 7149 reference_pc_update_7149_expr) reference_pc_update_7149_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma reference_pc_update_7149_safe : formal_typed_suffix_safe flat_memories 7149 reference_pc_update_7149_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma reference_pc_update_7149_nonregister : has_register 7149 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem reference_pc_update_7149_value invalid old current result width bits :
 eval_hfexpr_with_memory flat_memories reference_pc_update_7149_expr old old = Some (Gval (Fuint width) bits) ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 7149 result = Some (Gval (Fuint width) bits).
Proof.
 intros Eval Step. eapply formal_combinational_known_node;
 [exact reference_pc_update_7149_position|exact reference_pc_update_7149_safe|exact reference_pc_update_7149_nonregister|exact Eval|reflexivity|exact Step].
Qed.
Theorem reference_pc_update_7149_evaluation invalid old current result :
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 exists value, eval_hfexpr_with_memory flat_memories reference_pc_update_7149_expr old old = Some value.
Proof.
 intro Step.
 exact (formal_successful_node_evaluation 7228 flat_statements reference_pc_update_7149_tail 7149 reference_pc_update_7149_expr invalid flat_memories old false current result reference_pc_update_7149_position Step).
Qed.
Definition reference_pc_update_7433_expr := (@Econst VarOrder.T (Fuint 32) [::false; false; false; false; false; false; false; false; false; true; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false]).
Definition reference_pc_update_7433_tail := match straight_drop 7605 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma reference_pc_update_7433_position : straight_drop 7604 flat_statements = Some (@Qcons VarOrder.T (@Snode VarOrder.T 7433 reference_pc_update_7433_expr) reference_pc_update_7433_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma reference_pc_update_7433_safe : formal_typed_suffix_safe flat_memories 7433 reference_pc_update_7433_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma reference_pc_update_7433_nonregister : has_register 7433 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem reference_pc_update_7433_value invalid old current result width bits :
 eval_hfexpr_with_memory flat_memories reference_pc_update_7433_expr old old = Some (Gval (Fuint width) bits) ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 7433 result = Some (Gval (Fuint width) bits).
Proof.
 intros Eval Step. eapply formal_combinational_known_node;
 [exact reference_pc_update_7433_position|exact reference_pc_update_7433_safe|exact reference_pc_update_7433_nonregister|exact Eval|reflexivity|exact Step].
Qed.
Theorem reference_pc_update_7433_evaluation invalid old current result :
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 exists value, eval_hfexpr_with_memory flat_memories reference_pc_update_7433_expr old old = Some value.
Proof.
 intro Step.
 exact (formal_successful_node_evaluation 7604 flat_statements reference_pc_update_7433_tail 7433 reference_pc_update_7433_expr invalid flat_memories old false current result reference_pc_update_7433_position Step).
Qed.
Print Assumptions reference_pc_update_7433_value.
