Require Import CoreSocModel ComparisonNodes RegisterInvariants ScalarNodeFrames FormalTypedNodeFrames FormalTypedNodeEquation.
From Coq Require Import ZArith.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From firrtl Require Import Firrtl_with_implicit_widths Env_with_implicit_widths HiEnv_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Definition exception_pc_selection_7086_expr : hfexpr VarOrder.T := (@Econst VarOrder.T (Fuint 32) [::false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false]).
Definition exception_pc_selection_7086_tail := match straight_drop 7166 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma exception_pc_selection_7086_position : straight_drop 7165 flat_statements = Some (@Qcons VarOrder.T (@Snode VarOrder.T 7086 exception_pc_selection_7086_expr) exception_pc_selection_7086_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma exception_pc_selection_7086_safe : formal_typed_suffix_safe flat_memories 7086 exception_pc_selection_7086_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma exception_pc_selection_7086_nonregister : has_register 7086 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem exception_pc_selection_7086_value invalid old current result bits :
 eval_hfexpr_with_memory flat_memories exception_pc_selection_7086_expr old old = Some (Gval (Fuint 32) bits) ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 7086 result = Some (Gval (Fuint 32) bits).
Proof.
 intros Eval Step. eapply formal_combinational_known_node;
 [exact exception_pc_selection_7086_position|exact exception_pc_selection_7086_safe|exact exception_pc_selection_7086_nonregister|exact Eval|reflexivity|exact Step].
Qed.
Definition exception_pc_selection_7087_expr : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 6780)) (@Eref VarOrder.T (@Eid VarOrder.T 2812)) (@Eref VarOrder.T (@Eid VarOrder.T 7086))).
Definition exception_pc_selection_7087_tail := match straight_drop 7167 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma exception_pc_selection_7087_position : straight_drop 7166 flat_statements = Some (@Qcons VarOrder.T (@Snode VarOrder.T 7087 exception_pc_selection_7087_expr) exception_pc_selection_7087_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma exception_pc_selection_7087_safe : formal_typed_suffix_safe flat_memories 7087 exception_pc_selection_7087_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma exception_pc_selection_7087_nonregister : has_register 7087 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem exception_pc_selection_7087_value invalid old current result bits :
 eval_hfexpr_with_memory flat_memories exception_pc_selection_7087_expr old old = Some (Gval (Fuint 32) bits) ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 7087 result = Some (Gval (Fuint 32) bits).
Proof.
 intros Eval Step. eapply formal_combinational_known_node;
 [exact exception_pc_selection_7087_position|exact exception_pc_selection_7087_safe|exact exception_pc_selection_7087_nonregister|exact Eval|reflexivity|exact Step].
Qed.
Definition exception_pc_selection_7119_expr : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 1707)) (@Eref VarOrder.T (@Eid VarOrder.T 7087)) (@Eref VarOrder.T (@Eid VarOrder.T 7086))).
Definition exception_pc_selection_7119_tail := match straight_drop 7199 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma exception_pc_selection_7119_position : straight_drop 7198 flat_statements = Some (@Qcons VarOrder.T (@Snode VarOrder.T 7119 exception_pc_selection_7119_expr) exception_pc_selection_7119_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma exception_pc_selection_7119_safe : formal_typed_suffix_safe flat_memories 7119 exception_pc_selection_7119_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma exception_pc_selection_7119_nonregister : has_register 7119 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem exception_pc_selection_7119_value invalid old current result bits :
 eval_hfexpr_with_memory flat_memories exception_pc_selection_7119_expr old old = Some (Gval (Fuint 32) bits) ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 7119 result = Some (Gval (Fuint 32) bits).
Proof.
 intros Eval Step. eapply formal_combinational_known_node;
 [exact exception_pc_selection_7119_position|exact exception_pc_selection_7119_safe|exact exception_pc_selection_7119_nonregister|exact Eval|reflexivity|exact Step].
Qed.
Print Assumptions exception_pc_selection_7119_value.
