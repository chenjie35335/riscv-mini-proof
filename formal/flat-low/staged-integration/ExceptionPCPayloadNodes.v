Require Import CoreSocModel ComparisonNodes RegisterInvariants ScalarNodeFrames FormalTypedNodeFrames FormalTypedNodeEquation FormalDeclaredConnection FormalStatementSegments.
From Coq Require Import ZArith.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Definition exception_pc_2812_expr : hfexpr VarOrder.T := (@Eref VarOrder.T (@Eid VarOrder.T 1749)).
Definition exception_pc_2812_tail := match straight_drop 2892 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma exception_pc_2812_position : straight_drop 2891 flat_statements = Some (@Qcons VarOrder.T (@Snode VarOrder.T 2812 exception_pc_2812_expr) exception_pc_2812_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma exception_pc_2812_safe : formal_typed_suffix_safe flat_memories 2812 exception_pc_2812_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma exception_pc_2812_nonregister : has_register 2812 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem exception_pc_2812_value invalid old current result bits :
 VM.find 1749 old = Some (Gval (Fuint 32) bits) ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 2812 result = Some (Gval (Fuint 32) bits).
Proof.
 intros Source Step. eapply formal_combinational_known_node;
 [exact exception_pc_2812_position|exact exception_pc_2812_safe|exact exception_pc_2812_nonregister| |reflexivity|exact Step].
 unfold exception_pc_2812_expr. cbn [eval_hfexpr_with_memory eval_href_with_memory]. exact Source.
Qed.
Print Assumptions exception_pc_2812_value.
