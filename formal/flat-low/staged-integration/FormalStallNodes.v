Require Import RegisterInvariants CoreSocModel ComparisonNodes ScalarNodeFrames FormalTypedNodeFrames FormalTypedNodeEquation FormalDeclaredConnection FormalStatementSegments.
From Coq Require Import ZArith.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths Firrtl_with_implicit_widths HiEnv_with_implicit_widths
 HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Definition stall_expr_9215 := (@Eprim_unop VarOrder.T (Uextr 0 0) (@Eref VarOrder.T (@Eid VarOrder.T 1))).
Definition stall_tail_9215 := match straight_drop 10045 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma stall_position_9215 : straight_drop 10044 flat_statements = Some (@Qcons VarOrder.T (@Snode VarOrder.T 9215 stall_expr_9215) stall_tail_9215).
Proof. vm_compute. reflexivity. Qed.
Lemma stall_suffix_9215 : formal_typed_suffix_safe flat_memories 9215 stall_tail_9215.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma stall_nonregister_9215 : has_register 9215 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem stall_node_9215 invalid old current result value :
 eval_hfexpr_with_memory flat_memories stall_expr_9215 old old = Some value ->
 type_of_val value = Gtyp (Fuint 1) ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 9215 result = Some value.
Proof. intros Eval Typed Step. eapply formal_combinational_known_node;
 [exact stall_position_9215|exact stall_suffix_9215|exact stall_nonregister_9215|exact Eval|exact Typed|exact Step]. Qed.
Definition stall_expr_9216 := (@Eprim_binop VarOrder.T (Bcomp Beq) (@Eref VarOrder.T (@Eid VarOrder.T 9215)) (@Econst VarOrder.T (Fuint 1) [::false])).
Definition stall_tail_9216 := match straight_drop 10046 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma stall_position_9216 : straight_drop 10045 flat_statements = Some (@Qcons VarOrder.T (@Snode VarOrder.T 9216 stall_expr_9216) stall_tail_9216).
Proof. vm_compute. reflexivity. Qed.
Lemma stall_suffix_9216 : formal_typed_suffix_safe flat_memories 9216 stall_tail_9216.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma stall_nonregister_9216 : has_register 9216 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem stall_node_9216 invalid old current result value :
 eval_hfexpr_with_memory flat_memories stall_expr_9216 old old = Some value ->
 type_of_val value = Gtyp (Fuint 1) ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 9216 result = Some value.
Proof. intros Eval Typed Step. eapply formal_combinational_known_node;
 [exact stall_position_9216|exact stall_suffix_9216|exact stall_nonregister_9216|exact Eval|exact Typed|exact Step]. Qed.
Definition stall_expr_9217 := (@Eprim_unop VarOrder.T (Uextr 0 0) (@Eref VarOrder.T (@Eid VarOrder.T 1))).
Definition stall_tail_9217 := match straight_drop 10047 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma stall_position_9217 : straight_drop 10046 flat_statements = Some (@Qcons VarOrder.T (@Snode VarOrder.T 9217 stall_expr_9217) stall_tail_9217).
Proof. vm_compute. reflexivity. Qed.
Lemma stall_suffix_9217 : formal_typed_suffix_safe flat_memories 9217 stall_tail_9217.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma stall_nonregister_9217 : has_register 9217 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem stall_node_9217 invalid old current result value :
 eval_hfexpr_with_memory flat_memories stall_expr_9217 old old = Some value ->
 type_of_val value = Gtyp (Fuint 1) ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 9217 result = Some value.
Proof. intros Eval Typed Step. eapply formal_combinational_known_node;
 [exact stall_position_9217|exact stall_suffix_9217|exact stall_nonregister_9217|exact Eval|exact Typed|exact Step]. Qed.
Definition stall_expr_9218 := (@Eprim_binop VarOrder.T (Bcomp Beq) (@Eref VarOrder.T (@Eid VarOrder.T 9217)) (@Econst VarOrder.T (Fuint 1) [::false])).
Definition stall_tail_9218 := match straight_drop 10048 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma stall_position_9218 : straight_drop 10047 flat_statements = Some (@Qcons VarOrder.T (@Snode VarOrder.T 9218 stall_expr_9218) stall_tail_9218).
Proof. vm_compute. reflexivity. Qed.
Lemma stall_suffix_9218 : formal_typed_suffix_safe flat_memories 9218 stall_tail_9218.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma stall_nonregister_9218 : has_register 9218 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem stall_node_9218 invalid old current result value :
 eval_hfexpr_with_memory flat_memories stall_expr_9218 old old = Some value ->
 type_of_val value = Gtyp (Fuint 1) ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 9218 result = Some value.
Proof. intros Eval Typed Step. eapply formal_combinational_known_node;
 [exact stall_position_9218|exact stall_suffix_9218|exact stall_nonregister_9218|exact Eval|exact Typed|exact Step]. Qed.
Definition stall_expr_7763 := (@Eprim_binop VarOrder.T (Bcomp Beq) (@Eref VarOrder.T (@Eid VarOrder.T 74)) (@Econst VarOrder.T (Fuint 1) [::false])).
Definition stall_tail_7763 := match straight_drop 8270 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma stall_position_7763 : straight_drop 8269 flat_statements = Some (@Qcons VarOrder.T (@Snode VarOrder.T 7763 stall_expr_7763) stall_tail_7763).
Proof. vm_compute. reflexivity. Qed.
Lemma stall_suffix_7763 : formal_typed_suffix_safe flat_memories 7763 stall_tail_7763.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma stall_nonregister_7763 : has_register 7763 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem stall_node_7763 invalid old current result value :
 eval_hfexpr_with_memory flat_memories stall_expr_7763 old old = Some value ->
 type_of_val value = Gtyp (Fuint 1) ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 7763 result = Some value.
Proof. intros Eval Typed Step. eapply formal_combinational_known_node;
 [exact stall_position_7763|exact stall_suffix_7763|exact stall_nonregister_7763|exact Eval|exact Typed|exact Step]. Qed.
Definition stall_expr_7764 := (@Eprim_binop VarOrder.T (Bcomp Beq) (@Eref VarOrder.T (@Eid VarOrder.T 81)) (@Econst VarOrder.T (Fuint 1) [::false])).
Definition stall_tail_7764 := match straight_drop 8271 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma stall_position_7764 : straight_drop 8270 flat_statements = Some (@Qcons VarOrder.T (@Snode VarOrder.T 7764 stall_expr_7764) stall_tail_7764).
Proof. vm_compute. reflexivity. Qed.
Lemma stall_suffix_7764 : formal_typed_suffix_safe flat_memories 7764 stall_tail_7764.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma stall_nonregister_7764 : has_register 7764 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem stall_node_7764 invalid old current result value :
 eval_hfexpr_with_memory flat_memories stall_expr_7764 old old = Some value ->
 type_of_val value = Gtyp (Fuint 1) ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 7764 result = Some value.
Proof. intros Eval Typed Step. eapply formal_combinational_known_node;
 [exact stall_position_7764|exact stall_suffix_7764|exact stall_nonregister_7764|exact Eval|exact Typed|exact Step]. Qed.
Definition stall_expr_7765 := (@Eprim_binop VarOrder.T Bor (@Eref VarOrder.T (@Eid VarOrder.T 7763)) (@Eref VarOrder.T (@Eid VarOrder.T 7764))).
Definition stall_tail_7765 := match straight_drop 8272 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma stall_position_7765 : straight_drop 8271 flat_statements = Some (@Qcons VarOrder.T (@Snode VarOrder.T 7765 stall_expr_7765) stall_tail_7765).
Proof. vm_compute. reflexivity. Qed.
Lemma stall_suffix_7765 : formal_typed_suffix_safe flat_memories 7765 stall_tail_7765.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma stall_nonregister_7765 : has_register 7765 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem stall_node_7765 invalid old current result value :
 eval_hfexpr_with_memory flat_memories stall_expr_7765 old old = Some value ->
 type_of_val value = Gtyp (Fuint 1) ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 7765 result = Some value.
Proof. intros Eval Typed Step. eapply formal_combinational_known_node;
 [exact stall_position_7765|exact stall_suffix_7765|exact stall_nonregister_7765|exact Eval|exact Typed|exact Step]. Qed.
Print Assumptions stall_node_7765.
