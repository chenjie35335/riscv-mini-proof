Require Import RegisterInvariants CoreSocModel ComparisonNodes ScalarNodeFrames FormalTypedNodeFrames FormalTypedNodeEquation.
From Coq Require Import ZArith.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths Firrtl_with_implicit_widths HiEnv_with_implicit_widths
 HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Definition pipeline_expr_7849 := (@Ecast VarOrder.T AsUInt (@Eref VarOrder.T (@Eid VarOrder.T 65))).
Definition pipeline_tail_7849 := match straight_drop 8356 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma pipeline_position_7849 : straight_drop 8355 flat_statements = Some (@Qcons VarOrder.T (@Snode VarOrder.T 7849 pipeline_expr_7849) pipeline_tail_7849).
Proof. vm_compute. reflexivity. Qed.
Lemma pipeline_suffix_7849 : formal_typed_suffix_safe flat_memories 7849 pipeline_tail_7849.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma pipeline_nonregister_7849 : has_register 7849 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem pipeline_node_7849 invalid old current result value :
 eval_hfexpr_with_memory flat_memories pipeline_expr_7849 old old = Some value ->
 type_of_val value = Gtyp (Fuint 1) ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 7849 result = Some value.
Proof. intros Eval Typed Step. eapply formal_combinational_known_node;
 [exact pipeline_position_7849|exact pipeline_suffix_7849|exact pipeline_nonregister_7849|exact Eval|exact Typed|exact Step]. Qed.
Definition pipeline_expr_7850 := (@Eprim_binop VarOrder.T (Bcomp Beq) (@Eref VarOrder.T (@Eid VarOrder.T 7765)) (@Econst VarOrder.T (Fuint 1) [::false])).
Definition pipeline_tail_7850 := match straight_drop 8357 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma pipeline_position_7850 : straight_drop 8356 flat_statements = Some (@Qcons VarOrder.T (@Snode VarOrder.T 7850 pipeline_expr_7850) pipeline_tail_7850).
Proof. vm_compute. reflexivity. Qed.
Lemma pipeline_suffix_7850 : formal_typed_suffix_safe flat_memories 7850 pipeline_tail_7850.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma pipeline_nonregister_7850 : has_register 7850 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem pipeline_node_7850 invalid old current result value :
 eval_hfexpr_with_memory flat_memories pipeline_expr_7850 old old = Some value ->
 type_of_val value = Gtyp (Fuint 1) ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 7850 result = Some value.
Proof. intros Eval Typed Step. eapply formal_combinational_known_node;
 [exact pipeline_position_7850|exact pipeline_suffix_7850|exact pipeline_nonregister_7850|exact Eval|exact Typed|exact Step]. Qed.
Definition pipeline_expr_7851 := (@Eprim_binop VarOrder.T Band (@Eref VarOrder.T (@Eid VarOrder.T 7850)) (@Eref VarOrder.T (@Eid VarOrder.T 128))).
Definition pipeline_tail_7851 := match straight_drop 8358 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma pipeline_position_7851 : straight_drop 8357 flat_statements = Some (@Qcons VarOrder.T (@Snode VarOrder.T 7851 pipeline_expr_7851) pipeline_tail_7851).
Proof. vm_compute. reflexivity. Qed.
Lemma pipeline_suffix_7851 : formal_typed_suffix_safe flat_memories 7851 pipeline_tail_7851.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma pipeline_nonregister_7851 : has_register 7851 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem pipeline_node_7851 invalid old current result value :
 eval_hfexpr_with_memory flat_memories pipeline_expr_7851 old old = Some value ->
 type_of_val value = Gtyp (Fuint 1) ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 7851 result = Some value.
Proof. intros Eval Typed Step. eapply formal_combinational_known_node;
 [exact pipeline_position_7851|exact pipeline_suffix_7851|exact pipeline_nonregister_7851|exact Eval|exact Typed|exact Step]. Qed.
Definition pipeline_expr_7852 := (@Eprim_binop VarOrder.T Bor (@Eref VarOrder.T (@Eid VarOrder.T 7849)) (@Eref VarOrder.T (@Eid VarOrder.T 7851))).
Definition pipeline_tail_7852 := match straight_drop 8359 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma pipeline_position_7852 : straight_drop 8358 flat_statements = Some (@Qcons VarOrder.T (@Snode VarOrder.T 7852 pipeline_expr_7852) pipeline_tail_7852).
Proof. vm_compute. reflexivity. Qed.
Lemma pipeline_suffix_7852 : formal_typed_suffix_safe flat_memories 7852 pipeline_tail_7852.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma pipeline_nonregister_7852 : has_register 7852 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem pipeline_node_7852 invalid old current result value :
 eval_hfexpr_with_memory flat_memories pipeline_expr_7852 old old = Some value ->
 type_of_val value = Gtyp (Fuint 1) ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 7852 result = Some value.
Proof. intros Eval Typed Step. eapply formal_combinational_known_node;
 [exact pipeline_position_7852|exact pipeline_suffix_7852|exact pipeline_nonregister_7852|exact Eval|exact Typed|exact Step]. Qed.
Definition pipeline_expr_7853 := (@Eprim_binop VarOrder.T (Bcomp Beq) (@Eref VarOrder.T (@Eid VarOrder.T 7765)) (@Econst VarOrder.T (Fuint 1) [::false])).
Definition pipeline_tail_7853 := match straight_drop 8360 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma pipeline_position_7853 : straight_drop 8359 flat_statements = Some (@Qcons VarOrder.T (@Snode VarOrder.T 7853 pipeline_expr_7853) pipeline_tail_7853).
Proof. vm_compute. reflexivity. Qed.
Lemma pipeline_suffix_7853 : formal_typed_suffix_safe flat_memories 7853 pipeline_tail_7853.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma pipeline_nonregister_7853 : has_register 7853 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem pipeline_node_7853 invalid old current result value :
 eval_hfexpr_with_memory flat_memories pipeline_expr_7853 old old = Some value ->
 type_of_val value = Gtyp (Fuint 1) ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 7853 result = Some value.
Proof. intros Eval Typed Step. eapply formal_combinational_known_node;
 [exact pipeline_position_7853|exact pipeline_suffix_7853|exact pipeline_nonregister_7853|exact Eval|exact Typed|exact Step]. Qed.
Definition pipeline_expr_7854 := (@Eprim_binop VarOrder.T (Bcomp Beq) (@Eref VarOrder.T (@Eid VarOrder.T 128)) (@Econst VarOrder.T (Fuint 1) [::false])).
Definition pipeline_tail_7854 := match straight_drop 8361 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma pipeline_position_7854 : straight_drop 8360 flat_statements = Some (@Qcons VarOrder.T (@Snode VarOrder.T 7854 pipeline_expr_7854) pipeline_tail_7854).
Proof. vm_compute. reflexivity. Qed.
Lemma pipeline_suffix_7854 : formal_typed_suffix_safe flat_memories 7854 pipeline_tail_7854.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma pipeline_nonregister_7854 : has_register 7854 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem pipeline_node_7854 invalid old current result value :
 eval_hfexpr_with_memory flat_memories pipeline_expr_7854 old old = Some value ->
 type_of_val value = Gtyp (Fuint 1) ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 7854 result = Some value.
Proof. intros Eval Typed Step. eapply formal_combinational_known_node;
 [exact pipeline_position_7854|exact pipeline_suffix_7854|exact pipeline_nonregister_7854|exact Eval|exact Typed|exact Step]. Qed.
Definition pipeline_expr_7855 := (@Eprim_binop VarOrder.T Band (@Eref VarOrder.T (@Eid VarOrder.T 7853)) (@Eref VarOrder.T (@Eid VarOrder.T 7854))).
Definition pipeline_tail_7855 := match straight_drop 8362 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma pipeline_position_7855 : straight_drop 8361 flat_statements = Some (@Qcons VarOrder.T (@Snode VarOrder.T 7855 pipeline_expr_7855) pipeline_tail_7855).
Proof. vm_compute. reflexivity. Qed.
Lemma pipeline_suffix_7855 : formal_typed_suffix_safe flat_memories 7855 pipeline_tail_7855.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma pipeline_nonregister_7855 : has_register 7855 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem pipeline_node_7855 invalid old current result value :
 eval_hfexpr_with_memory flat_memories pipeline_expr_7855 old old = Some value ->
 type_of_val value = Gtyp (Fuint 1) ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 7855 result = Some value.
Proof. intros Eval Typed Step. eapply formal_combinational_known_node;
 [exact pipeline_position_7855|exact pipeline_suffix_7855|exact pipeline_nonregister_7855|exact Eval|exact Typed|exact Step]. Qed.
Print Assumptions pipeline_node_7855.
