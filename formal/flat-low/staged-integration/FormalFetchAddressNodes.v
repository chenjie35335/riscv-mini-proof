Require Import RegisterInvariants CoreSocModel ComparisonNodes ScalarNodeFrames FormalTypedNodeFrames FormalTypedNodeEquation.
From Coq Require Import ZArith.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths Firrtl_with_implicit_widths HiEnv_with_implicit_widths
 HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Definition fetch_address_expr_9181 := (@Eprim_binop VarOrder.T Bdiv (@Eref VarOrder.T (@Eid VarOrder.T 30)) (@Econst VarOrder.T (Fuint 3) [::false; false; true])).
Definition fetch_address_tail_9181 := match straight_drop 10011 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma fetch_address_position_9181 : straight_drop 10010 flat_statements = Some (@Qcons VarOrder.T (@Snode VarOrder.T 9181 fetch_address_expr_9181) fetch_address_tail_9181).
Proof. vm_compute. reflexivity. Qed.
Lemma fetch_address_suffix_9181 : formal_typed_suffix_safe flat_memories 9181 fetch_address_tail_9181.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma fetch_address_nonregister_9181 : has_register 9181 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem fetch_address_node_9181 invalid old current result value :
 eval_hfexpr_with_memory flat_memories fetch_address_expr_9181 old old = Some value ->
 type_of_val value = Gtyp (Fuint 32) ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 9181 result = Some value.
Proof. intros Eval Typed Step. eapply formal_combinational_known_node;
 [exact fetch_address_position_9181|exact fetch_address_suffix_9181|exact fetch_address_nonregister_9181|exact Eval|exact Typed|exact Step]. Qed.
Definition fetch_address_expr_9219 := (@Eprim_unop VarOrder.T (Uextr 3 0) (@Eref VarOrder.T (@Eid VarOrder.T 9181))).
Definition fetch_address_tail_9219 := match straight_drop 10049 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma fetch_address_position_9219 : straight_drop 10048 flat_statements = Some (@Qcons VarOrder.T (@Snode VarOrder.T 9219 fetch_address_expr_9219) fetch_address_tail_9219).
Proof. vm_compute. reflexivity. Qed.
Lemma fetch_address_suffix_9219 : formal_typed_suffix_safe flat_memories 9219 fetch_address_tail_9219.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma fetch_address_nonregister_9219 : has_register 9219 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem fetch_address_node_9219 invalid old current result value :
 eval_hfexpr_with_memory flat_memories fetch_address_expr_9219 old old = Some value ->
 type_of_val value = Gtyp (Fuint 4) ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 9219 result = Some value.
Proof. intros Eval Typed Step. eapply formal_combinational_known_node;
 [exact fetch_address_position_9219|exact fetch_address_suffix_9219|exact fetch_address_nonregister_9219|exact Eval|exact Typed|exact Step]. Qed.
Print Assumptions fetch_address_node_9219.
