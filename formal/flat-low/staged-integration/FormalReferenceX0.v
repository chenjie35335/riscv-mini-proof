Require Import RegisterInvariants CoreSocModel ComparisonNodes ScalarNodeFrames FormalTypedNodeFrames FormalTypedNodeEquation.
From Coq Require Import ZArith.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths Firrtl_with_implicit_widths HiEnv_with_implicit_widths
 HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Definition reference_x0_expr_3255 := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 1707)) (@Econst VarOrder.T (Fuint 1) [::false]) (@Eref VarOrder.T (@Eid VarOrder.T 2177))).
Definition reference_x0_tail_3255 := match straight_drop 3335 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma reference_x0_position_3255 : straight_drop 3334 flat_statements = Some (@Qcons VarOrder.T (@Snode VarOrder.T 3255 reference_x0_expr_3255) reference_x0_tail_3255).
Proof. vm_compute. reflexivity. Qed.
Lemma reference_x0_suffix_3255 : formal_typed_suffix_safe flat_memories 3255 reference_x0_tail_3255.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma reference_x0_nonregister_3255 : has_register 3255 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem reference_x0_node_3255 invalid old current result value :
 eval_hfexpr_with_memory flat_memories reference_x0_expr_3255 old old = Some value ->
 type_of_val value = Gtyp (Fuint 32) ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 3255 result = Some value.
Proof. intros Eval Typed Step. eapply formal_combinational_known_node;
 [exact reference_x0_position_3255|exact reference_x0_suffix_3255|exact reference_x0_nonregister_3255|exact Eval|exact Typed|exact Step]. Qed.
Definition reference_x0_expr_3256 := (@Eref VarOrder.T (@Eid VarOrder.T 3255)).
Definition reference_x0_tail_3256 := match straight_drop 3336 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma reference_x0_position_3256 : straight_drop 3335 flat_statements = Some (@Qcons VarOrder.T (@Snode VarOrder.T 3256 reference_x0_expr_3256) reference_x0_tail_3256).
Proof. vm_compute. reflexivity. Qed.
Lemma reference_x0_suffix_3256 : formal_typed_suffix_safe flat_memories 3256 reference_x0_tail_3256.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma reference_x0_nonregister_3256 : has_register 3256 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem reference_x0_node_3256 invalid old current result value :
 eval_hfexpr_with_memory flat_memories reference_x0_expr_3256 old old = Some value ->
 type_of_val value = Gtyp (Fuint 32) ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 3256 result = Some value.
Proof. intros Eval Typed Step. eapply formal_combinational_known_node;
 [exact reference_x0_position_3256|exact reference_x0_suffix_3256|exact reference_x0_nonregister_3256|exact Eval|exact Typed|exact Step]. Qed.
From nbits Require Import NBits.
Lemma formal_reference_x0_valid old value :
 VM.find 1707 old = Some (Gval (Fuint 1) [::true]) ->
 VM.find 2177 old = Some value -> type_of_val value = Gtyp (Fuint 32) ->
 eval_hfexpr_with_memory flat_memories reference_x0_expr_3255 old old = Some (Gval (Fuint 32) (zeros 32)).
Proof.
 intros Valid Source Typed.
 cbn [reference_x0_expr_3255 eval_hfexpr_with_memory eval_href_with_memory]. rewrite Valid.
 cbn [is_zero]. unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite Source. cbn [option_map]. rewrite Typed. reflexivity.
Qed.
Theorem formal_reference_x0_iteration invalid old current result value :
 VM.find 1707 old = Some (Gval (Fuint 1) [::true]) ->
 VM.find 2177 old = Some value -> type_of_val value = Gtyp (Fuint 32) ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 3255 result = Some (Gval (Fuint 32) (zeros 32)).
Proof.
 intros Valid Source Typed Step.
 exact (reference_x0_node_3255 invalid old current result _
  (formal_reference_x0_valid old value Valid Source Typed) (Logic.eq_refl _) Step).
Qed.
Print Assumptions formal_reference_x0_iteration.
