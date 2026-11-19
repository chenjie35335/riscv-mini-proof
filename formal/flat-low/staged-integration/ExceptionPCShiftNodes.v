Require Import CoreSocModel ComparisonNodes RegisterInvariants ScalarNodeFrames FormalTypedNodeFrames FormalTypedNodeEquation.
From Coq Require Import ZArith.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From firrtl Require Import Firrtl_with_implicit_widths Env_with_implicit_widths HiEnv_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Definition exception_pc_shift_771_expr : hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Ushr 2) (@Eref VarOrder.T (@Eid VarOrder.T 121))).
Definition exception_pc_shift_771_tail := match straight_drop 749 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma exception_pc_shift_771_position : straight_drop 748 flat_statements = Some (@Qcons VarOrder.T (@Snode VarOrder.T 771 exception_pc_shift_771_expr) exception_pc_shift_771_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma exception_pc_shift_771_safe : formal_typed_suffix_safe flat_memories 771 exception_pc_shift_771_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma exception_pc_shift_771_nonregister : has_register 771 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem exception_pc_shift_771_value invalid old current result bits :
 eval_hfexpr_with_memory flat_memories exception_pc_shift_771_expr old old = Some (Gval (Fuint 30) bits) ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 771 result = Some (Gval (Fuint 30) bits).
Proof.
 intros Eval Step. eapply formal_combinational_known_node;
 [exact exception_pc_shift_771_position|exact exception_pc_shift_771_safe|exact exception_pc_shift_771_nonregister|exact Eval|reflexivity|exact Step].
Qed.
Definition exception_pc_shift_772_expr : hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Ushl 2) (@Eref VarOrder.T (@Eid VarOrder.T 771))).
Definition exception_pc_shift_772_tail := match straight_drop 750 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma exception_pc_shift_772_position : straight_drop 749 flat_statements = Some (@Qcons VarOrder.T (@Snode VarOrder.T 772 exception_pc_shift_772_expr) exception_pc_shift_772_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma exception_pc_shift_772_safe : formal_typed_suffix_safe flat_memories 772 exception_pc_shift_772_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma exception_pc_shift_772_nonregister : has_register 772 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem exception_pc_shift_772_value invalid old current result bits :
 eval_hfexpr_with_memory flat_memories exception_pc_shift_772_expr old old = Some (Gval (Fuint 32) bits) ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 772 result = Some (Gval (Fuint 32) bits).
Proof.
 intros Eval Step. eapply formal_combinational_known_node;
 [exact exception_pc_shift_772_position|exact exception_pc_shift_772_safe|exact exception_pc_shift_772_nonregister|exact Eval|reflexivity|exact Step].
Qed.
Print Assumptions exception_pc_shift_772_value.
