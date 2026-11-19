Require Import ConcreteFalseMuxSource.
Require Import ConcreteSelectedMuxSource FormalSuccessfulNodeEvaluation.
Require Import RegisterInvariants CoreSocModel ComparisonNodes ScalarNodeFrames FormalTypedNodeFrames FormalTypedNodeEquation.
From Coq Require Import ZArith.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths Firrtl_with_implicit_widths HiEnv_with_implicit_widths
 HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Definition pc_choice_7777_expr := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 7776)) (@Eref VarOrder.T (@Eid VarOrder.T 7768)) (@Eref VarOrder.T (@Eid VarOrder.T 7770))).
Definition pc_choice_7777_tail := match straight_drop 8284 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma pc_choice_7777_position : straight_drop 8283 flat_statements = Some (@Qcons VarOrder.T (@Snode VarOrder.T 7777 pc_choice_7777_expr) pc_choice_7777_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma pc_choice_7777_suffix : formal_typed_suffix_safe flat_memories 7777 pc_choice_7777_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma pc_choice_7777_nonregister : has_register 7777 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem pc_choice_7777_true invalid old current result width word :
 VM.find 7776 old = Some (Gval (Fuint 1) [::true]) ->
 VM.find 7768 old = Some (Gval (Fuint width) word) ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 exists result_width bits, VM.find 7777 result = Some (Gval (Fuint result_width) bits).
Proof.
 intros Condition Value Step.
 destruct (formal_successful_node_evaluation 8283 flat_statements pc_choice_7777_tail 7777 pc_choice_7777_expr invalid flat_memories old false current result pc_choice_7777_position Step) as [value Eval].
 change (eval_hfexpr_with_memory flat_memories pc_choice_7777_expr old old = Some value) in Eval.
 destruct (selected_uint_mux_source_concrete flat_memories old 7776 7768 7770 width word value Condition Value Eval) as [result_width [bits Concrete]].
 subst value. exists result_width, bits. eapply formal_combinational_known_node;
 [exact pc_choice_7777_position|exact pc_choice_7777_suffix|exact pc_choice_7777_nonregister|exact Eval|reflexivity|exact Step].
Qed.
Theorem pc_choice_7777_false invalid old current result width word :
 VM.find 7776 old = Some (Gval (Fuint 1) [::false]) ->
 VM.find 7770 old = Some (Gval (Fuint width) word) ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 exists result_width bits, VM.find 7777 result = Some (Gval (Fuint result_width) bits).
Proof.
 intros Condition Value Step.
 destruct (formal_successful_node_evaluation 8283 flat_statements pc_choice_7777_tail 7777 pc_choice_7777_expr invalid flat_memories old false current result pc_choice_7777_position Step) as [value Eval].
 change (eval_hfexpr_with_memory flat_memories pc_choice_7777_expr old old = Some value) in Eval.
 destruct (false_uint_mux_source_concrete flat_memories old 7776 7768 7770 width word value Condition Value Eval) as [result_width [bits Concrete]].
 subst value. exists result_width, bits. eapply formal_combinational_known_node;
 [exact pc_choice_7777_position|exact pc_choice_7777_suffix|exact pc_choice_7777_nonregister|exact Eval|reflexivity|exact Step].
Qed.
Definition pc_choice_7778_expr := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 7773)) (@Eref VarOrder.T (@Eid VarOrder.T 7775)) (@Eref VarOrder.T (@Eid VarOrder.T 7777))).
Definition pc_choice_7778_tail := match straight_drop 8285 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma pc_choice_7778_position : straight_drop 8284 flat_statements = Some (@Qcons VarOrder.T (@Snode VarOrder.T 7778 pc_choice_7778_expr) pc_choice_7778_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma pc_choice_7778_suffix : formal_typed_suffix_safe flat_memories 7778 pc_choice_7778_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma pc_choice_7778_nonregister : has_register 7778 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem pc_choice_7778_true invalid old current result width word :
 VM.find 7773 old = Some (Gval (Fuint 1) [::true]) ->
 VM.find 7775 old = Some (Gval (Fuint width) word) ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 exists result_width bits, VM.find 7778 result = Some (Gval (Fuint result_width) bits).
Proof.
 intros Condition Value Step.
 destruct (formal_successful_node_evaluation 8284 flat_statements pc_choice_7778_tail 7778 pc_choice_7778_expr invalid flat_memories old false current result pc_choice_7778_position Step) as [value Eval].
 change (eval_hfexpr_with_memory flat_memories pc_choice_7778_expr old old = Some value) in Eval.
 destruct (selected_uint_mux_source_concrete flat_memories old 7773 7775 7777 width word value Condition Value Eval) as [result_width [bits Concrete]].
 subst value. exists result_width, bits. eapply formal_combinational_known_node;
 [exact pc_choice_7778_position|exact pc_choice_7778_suffix|exact pc_choice_7778_nonregister|exact Eval|reflexivity|exact Step].
Qed.
Theorem pc_choice_7778_false invalid old current result width word :
 VM.find 7773 old = Some (Gval (Fuint 1) [::false]) ->
 VM.find 7777 old = Some (Gval (Fuint width) word) ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 exists result_width bits, VM.find 7778 result = Some (Gval (Fuint result_width) bits).
Proof.
 intros Condition Value Step.
 destruct (formal_successful_node_evaluation 8284 flat_statements pc_choice_7778_tail 7778 pc_choice_7778_expr invalid flat_memories old false current result pc_choice_7778_position Step) as [value Eval].
 change (eval_hfexpr_with_memory flat_memories pc_choice_7778_expr old old = Some value) in Eval.
 destruct (false_uint_mux_source_concrete flat_memories old 7773 7775 7777 width word value Condition Value Eval) as [result_width [bits Concrete]].
 subst value. exists result_width, bits. eapply formal_combinational_known_node;
 [exact pc_choice_7778_position|exact pc_choice_7778_suffix|exact pc_choice_7778_nonregister|exact Eval|reflexivity|exact Step].
Qed.
Definition pc_choice_7779_expr := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 7771)) (@Eref VarOrder.T (@Eid VarOrder.T 130)) (@Eref VarOrder.T (@Eid VarOrder.T 7778))).
Definition pc_choice_7779_tail := match straight_drop 8286 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma pc_choice_7779_position : straight_drop 8285 flat_statements = Some (@Qcons VarOrder.T (@Snode VarOrder.T 7779 pc_choice_7779_expr) pc_choice_7779_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma pc_choice_7779_suffix : formal_typed_suffix_safe flat_memories 7779 pc_choice_7779_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma pc_choice_7779_nonregister : has_register 7779 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem pc_choice_7779_true invalid old current result width word :
 VM.find 7771 old = Some (Gval (Fuint 1) [::true]) ->
 VM.find 130 old = Some (Gval (Fuint width) word) ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 exists result_width bits, VM.find 7779 result = Some (Gval (Fuint result_width) bits).
Proof.
 intros Condition Value Step.
 destruct (formal_successful_node_evaluation 8285 flat_statements pc_choice_7779_tail 7779 pc_choice_7779_expr invalid flat_memories old false current result pc_choice_7779_position Step) as [value Eval].
 change (eval_hfexpr_with_memory flat_memories pc_choice_7779_expr old old = Some value) in Eval.
 destruct (selected_uint_mux_source_concrete flat_memories old 7771 130 7778 width word value Condition Value Eval) as [result_width [bits Concrete]].
 subst value. exists result_width, bits. eapply formal_combinational_known_node;
 [exact pc_choice_7779_position|exact pc_choice_7779_suffix|exact pc_choice_7779_nonregister|exact Eval|reflexivity|exact Step].
Qed.
Theorem pc_choice_7779_false invalid old current result width word :
 VM.find 7771 old = Some (Gval (Fuint 1) [::false]) ->
 VM.find 7778 old = Some (Gval (Fuint width) word) ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 exists result_width bits, VM.find 7779 result = Some (Gval (Fuint result_width) bits).
Proof.
 intros Condition Value Step.
 destruct (formal_successful_node_evaluation 8285 flat_statements pc_choice_7779_tail 7779 pc_choice_7779_expr invalid flat_memories old false current result pc_choice_7779_position Step) as [value Eval].
 change (eval_hfexpr_with_memory flat_memories pc_choice_7779_expr old old = Some value) in Eval.
 destruct (false_uint_mux_source_concrete flat_memories old 7771 130 7778 width word value Condition Value Eval) as [result_width [bits Concrete]].
 subst value. exists result_width, bits. eapply formal_combinational_known_node;
 [exact pc_choice_7779_position|exact pc_choice_7779_suffix|exact pc_choice_7779_nonregister|exact Eval|reflexivity|exact Step].
Qed.
Definition pc_choice_7780_expr := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 128)) (@Eref VarOrder.T (@Eid VarOrder.T 129)) (@Eref VarOrder.T (@Eid VarOrder.T 7779))).
Definition pc_choice_7780_tail := match straight_drop 8287 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma pc_choice_7780_position : straight_drop 8286 flat_statements = Some (@Qcons VarOrder.T (@Snode VarOrder.T 7780 pc_choice_7780_expr) pc_choice_7780_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma pc_choice_7780_suffix : formal_typed_suffix_safe flat_memories 7780 pc_choice_7780_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma pc_choice_7780_nonregister : has_register 7780 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem pc_choice_7780_true invalid old current result width word :
 VM.find 128 old = Some (Gval (Fuint 1) [::true]) ->
 VM.find 129 old = Some (Gval (Fuint width) word) ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 exists result_width bits, VM.find 7780 result = Some (Gval (Fuint result_width) bits).
Proof.
 intros Condition Value Step.
 destruct (formal_successful_node_evaluation 8286 flat_statements pc_choice_7780_tail 7780 pc_choice_7780_expr invalid flat_memories old false current result pc_choice_7780_position Step) as [value Eval].
 change (eval_hfexpr_with_memory flat_memories pc_choice_7780_expr old old = Some value) in Eval.
 destruct (selected_uint_mux_source_concrete flat_memories old 128 129 7779 width word value Condition Value Eval) as [result_width [bits Concrete]].
 subst value. exists result_width, bits. eapply formal_combinational_known_node;
 [exact pc_choice_7780_position|exact pc_choice_7780_suffix|exact pc_choice_7780_nonregister|exact Eval|reflexivity|exact Step].
Qed.
Theorem pc_choice_7780_false invalid old current result width word :
 VM.find 128 old = Some (Gval (Fuint 1) [::false]) ->
 VM.find 7779 old = Some (Gval (Fuint width) word) ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 exists result_width bits, VM.find 7780 result = Some (Gval (Fuint result_width) bits).
Proof.
 intros Condition Value Step.
 destruct (formal_successful_node_evaluation 8286 flat_statements pc_choice_7780_tail 7780 pc_choice_7780_expr invalid flat_memories old false current result pc_choice_7780_position Step) as [value Eval].
 change (eval_hfexpr_with_memory flat_memories pc_choice_7780_expr old old = Some value) in Eval.
 destruct (false_uint_mux_source_concrete flat_memories old 128 129 7779 width word value Condition Value Eval) as [result_width [bits Concrete]].
 subst value. exists result_width, bits. eapply formal_combinational_known_node;
 [exact pc_choice_7780_position|exact pc_choice_7780_suffix|exact pc_choice_7780_nonregister|exact Eval|reflexivity|exact Step].
Qed.
Print Assumptions pc_choice_7780_false.
