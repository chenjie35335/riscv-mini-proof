Require Import ConcreteSelectedMuxSource FormalSuccessfulNodeEvaluation.
Require Import RegisterInvariants CoreSocModel ComparisonNodes ScalarNodeFrames FormalTypedNodeFrames FormalTypedNodeEquation.
From Coq Require Import ZArith.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths Firrtl_with_implicit_widths HiEnv_with_implicit_widths
 HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Definition pc_selected_expr := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 7765)) (@Eref VarOrder.T (@Eid VarOrder.T 7768)) (@Eref VarOrder.T (@Eid VarOrder.T 7780))).
Definition pc_selected_tail := match straight_drop 8288 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma pc_selected_position : straight_drop 8287 flat_statements = Some (@Qcons VarOrder.T (@Snode VarOrder.T 7781 pc_selected_expr) pc_selected_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma pc_selected_suffix : formal_typed_suffix_safe flat_memories 7781 pc_selected_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma pc_selected_nonregister : has_register 7781 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem stalled_pc_concrete invalid old current result pc_width pc :
 VM.find 7765 old = Some (Gval (Fuint 1) [::true]) ->
 VM.find 7768 old = Some (Gval (Fuint pc_width) pc) ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 exists width word, VM.find 7781 result = Some (Gval (Fuint width) word).
Proof.
 intros Stall PC Step.
 destruct (formal_successful_node_evaluation 8287 flat_statements pc_selected_tail 7781 pc_selected_expr invalid flat_memories old false current result pc_selected_position Step)
 as [value Eval].
 change (eval_hfexpr_with_memory flat_memories pc_selected_expr old old = Some value) in Eval.
 destruct (selected_uint_mux_source_concrete flat_memories old 7765 7768 7780 pc_width pc value Stall PC Eval)
 as [width [word Concrete]]. subst value.
 exists width, word. eapply formal_combinational_known_node;
 [exact pc_selected_position|exact pc_selected_suffix|exact pc_selected_nonregister|exact Eval|reflexivity|exact Step].
Qed.
Print Assumptions stalled_pc_concrete.
