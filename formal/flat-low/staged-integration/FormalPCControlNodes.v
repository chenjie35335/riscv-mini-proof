Require Import RegisterInvariants CoreSocModel ComparisonNodes ScalarNodeFrames FormalTypedNodeFrames FormalTypedNodeEquation.
From Coq Require Import ZArith.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths Firrtl_with_implicit_widths HiEnv_with_implicit_widths
 HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Definition pc_control_expr_7771 := (@Eprim_binop VarOrder.T (Bcomp Beq) (@Eref VarOrder.T (@Eid VarOrder.T 84)) (@Econst VarOrder.T (Fuint 2) [::true; true])).
Definition pc_control_tail_7771 := match straight_drop 8278 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma pc_control_position_7771 : straight_drop 8277 flat_statements = Some (@Qcons VarOrder.T (@Snode VarOrder.T 7771 pc_control_expr_7771) pc_control_tail_7771).
Proof. vm_compute. reflexivity. Qed.
Lemma pc_control_suffix_7771 : formal_typed_suffix_safe flat_memories 7771 pc_control_tail_7771.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma pc_control_nonregister_7771 : has_register 7771 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem pc_control_node_7771 invalid old current result value :
 eval_hfexpr_with_memory flat_memories pc_control_expr_7771 old old = Some value ->
 type_of_val value = Gtyp (Fuint 1) ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 7771 result = Some value.
Proof. intros Eval Typed Step. eapply formal_combinational_known_node;
 [exact pc_control_position_7771|exact pc_control_suffix_7771|exact pc_control_nonregister_7771|exact Eval|exact Typed|exact Step]. Qed.
Definition pc_control_expr_7772 := (@Eprim_binop VarOrder.T (Bcomp Beq) (@Eref VarOrder.T (@Eid VarOrder.T 84)) (@Econst VarOrder.T (Fuint 2) [::true; false])).
Definition pc_control_tail_7772 := match straight_drop 8279 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma pc_control_position_7772 : straight_drop 8278 flat_statements = Some (@Qcons VarOrder.T (@Snode VarOrder.T 7772 pc_control_expr_7772) pc_control_tail_7772).
Proof. vm_compute. reflexivity. Qed.
Lemma pc_control_suffix_7772 : formal_typed_suffix_safe flat_memories 7772 pc_control_tail_7772.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma pc_control_nonregister_7772 : has_register 7772 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem pc_control_node_7772 invalid old current result value :
 eval_hfexpr_with_memory flat_memories pc_control_expr_7772 old old = Some value ->
 type_of_val value = Gtyp (Fuint 1) ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 7772 result = Some value.
Proof. intros Eval Typed Step. eapply formal_combinational_known_node;
 [exact pc_control_position_7772|exact pc_control_suffix_7772|exact pc_control_nonregister_7772|exact Eval|exact Typed|exact Step]. Qed.
Definition pc_control_expr_7773 := (@Eprim_binop VarOrder.T Bor (@Eref VarOrder.T (@Eid VarOrder.T 7772)) (@Eref VarOrder.T (@Eid VarOrder.T 1360))).
Definition pc_control_tail_7773 := match straight_drop 8280 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma pc_control_position_7773 : straight_drop 8279 flat_statements = Some (@Qcons VarOrder.T (@Snode VarOrder.T 7773 pc_control_expr_7773) pc_control_tail_7773).
Proof. vm_compute. reflexivity. Qed.
Lemma pc_control_suffix_7773 : formal_typed_suffix_safe flat_memories 7773 pc_control_tail_7773.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma pc_control_nonregister_7773 : has_register 7773 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem pc_control_node_7773 invalid old current result value :
 eval_hfexpr_with_memory flat_memories pc_control_expr_7773 old old = Some value ->
 type_of_val value = Gtyp (Fuint 1) ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 7773 result = Some value.
Proof. intros Eval Typed Step. eapply formal_combinational_known_node;
 [exact pc_control_position_7773|exact pc_control_suffix_7773|exact pc_control_nonregister_7773|exact Eval|exact Typed|exact Step]. Qed.
Definition pc_control_expr_7776 := (@Eprim_binop VarOrder.T (Bcomp Beq) (@Eref VarOrder.T (@Eid VarOrder.T 84)) (@Econst VarOrder.T (Fuint 2) [::false; true])).
Definition pc_control_tail_7776 := match straight_drop 8283 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma pc_control_position_7776 : straight_drop 8282 flat_statements = Some (@Qcons VarOrder.T (@Snode VarOrder.T 7776 pc_control_expr_7776) pc_control_tail_7776).
Proof. vm_compute. reflexivity. Qed.
Lemma pc_control_suffix_7776 : formal_typed_suffix_safe flat_memories 7776 pc_control_tail_7776.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma pc_control_nonregister_7776 : has_register 7776 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem pc_control_node_7776 invalid old current result value :
 eval_hfexpr_with_memory flat_memories pc_control_expr_7776 old old = Some value ->
 type_of_val value = Gtyp (Fuint 1) ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 7776 result = Some value.
Proof. intros Eval Typed Step. eapply formal_combinational_known_node;
 [exact pc_control_position_7776|exact pc_control_suffix_7776|exact pc_control_nonregister_7776|exact Eval|exact Typed|exact Step]. Qed.
Print Assumptions pc_control_node_7776.
