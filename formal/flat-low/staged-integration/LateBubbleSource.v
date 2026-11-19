Require Import CoreSocModel ComparisonNodes FormalNodeEquation MemorySuffixCertificates MemoryWriteFrames ScalarNodeFrames RegisterInvariants.
From Coq Require Import ZArith.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths Firrtl_with_implicit_widths HiEnv_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Definition late_bubble_expr_7946 := (@Eprim_binop VarOrder.T Bor (@Eref VarOrder.T (@Eid VarOrder.T 7945)) (@Eref VarOrder.T (@Eid VarOrder.T 128))).
Definition late_bubble_tail_7946 := match straight_drop 8453 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma late_bubble_position_7946 : straight_drop 8452 flat_statements = Some (@Qcons VarOrder.T (@Snode VarOrder.T 7946 late_bubble_expr_7946) late_bubble_tail_7946).
Proof. vm_compute. reflexivity. Qed.
Lemma late_bubble_suffix_7946 : memory_suffix_safe flat_memories 7946 late_bubble_tail_7946.
Proof. apply memory_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma late_bubble_nonregister_7946 : has_register 7946 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem late_bubble_equation_7946 invalid old current result :
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 7946 result = eval_hfexpr_with_memory flat_memories late_bubble_expr_7946 old old.
Proof.
 intro Step. exact (formal_combinational_node_equation _ _ _ _ _ invalid flat_memories old current result
 late_bubble_position_7946 late_bubble_suffix_7946 late_bubble_nonregister_7946 Step).
Qed.
Theorem late_bubble_source_value invalid old current result early exception :
 VM.find 7945 old = Some (Gval (Fuint 1) [::early]) ->
 VM.find 128 old = Some (Gval (Fuint 1) [::exception]) ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 7946 result = Some (Gval (Fuint 1) [::early || exception]).
Proof.
 intros Early Exception Step.
 rewrite (late_bubble_equation_7946 invalid old current result Step).
 cbn [late_bubble_expr_7946 eval_hfexpr_with_memory eval_href_with_memory].
 rewrite Early Exception. destruct early, exception; reflexivity.
Qed.
Print Assumptions late_bubble_source_value.
