Require Import CoreSocModel ComparisonNodes RegisterInvariants ScalarNodeFrames FormalTypedNodeFrames FormalTypedNodeEquation FormalDeclaredConnection FormalStatementSegments.
From Coq Require Import ZArith.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Definition exception_instruction_777_expr : hfexpr VarOrder.T := (@Eref VarOrder.T (@Eid VarOrder.T 123)).
Definition exception_instruction_777_tail := match straight_drop 755 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma exception_instruction_777_position : straight_drop 754 flat_statements = Some (@Qcons VarOrder.T (@Snode VarOrder.T 777 exception_instruction_777_expr) exception_instruction_777_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma exception_instruction_777_safe : formal_typed_suffix_safe flat_memories 777 exception_instruction_777_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma exception_instruction_777_nonregister : has_register 777 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem exception_instruction_777_value invalid old current result bits :
 VM.find 123 old = Some (Gval (Fuint 32) bits) ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 777 result = Some (Gval (Fuint 32) bits).
Proof.
 intros Source Step. eapply formal_combinational_known_node;
 [exact exception_instruction_777_position|exact exception_instruction_777_safe|exact exception_instruction_777_nonregister| |reflexivity|exact Step].
 unfold exception_instruction_777_expr. cbn [eval_hfexpr_with_memory eval_href_with_memory]. exact Source.
Qed.
Definition exception_instruction_7207_expr : hfexpr VarOrder.T := (@Eref VarOrder.T (@Eid VarOrder.T 7120)).
Definition exception_instruction_7207_tail := match straight_drop 7287 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma exception_instruction_7207_position : straight_drop 7286 flat_statements = Some (@Qcons VarOrder.T (@Snode VarOrder.T 7207 exception_instruction_7207_expr) exception_instruction_7207_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma exception_instruction_7207_safe : formal_typed_suffix_safe flat_memories 7207 exception_instruction_7207_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma exception_instruction_7207_nonregister : has_register 7207 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem exception_instruction_7207_value invalid old current result bits :
 VM.find 7120 old = Some (Gval (Fuint 32) bits) ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 7207 result = Some (Gval (Fuint 32) bits).
Proof.
 intros Source Step. eapply formal_combinational_known_node;
 [exact exception_instruction_7207_position|exact exception_instruction_7207_safe|exact exception_instruction_7207_nonregister| |reflexivity|exact Step].
 unfold exception_instruction_7207_expr. cbn [eval_hfexpr_with_memory eval_href_with_memory]. exact Source.
Qed.
Definition exception_instruction_8157_expr : hfexpr VarOrder.T := (@Eref VarOrder.T (@Eid VarOrder.T 138)).
Definition exception_instruction_8157_tail := match straight_drop 8664 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma exception_instruction_8157_position : straight_drop 8663 flat_statements = Some (@Qcons VarOrder.T (@Snode VarOrder.T 8157 exception_instruction_8157_expr) exception_instruction_8157_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma exception_instruction_8157_safe : formal_typed_suffix_safe flat_memories 8157 exception_instruction_8157_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma exception_instruction_8157_nonregister : has_register 8157 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem exception_instruction_8157_value invalid old current result bits :
 VM.find 138 old = Some (Gval (Fuint 32) bits) ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 8157 result = Some (Gval (Fuint 32) bits).
Proof.
 intros Source Step. eapply formal_combinational_known_node;
 [exact exception_instruction_8157_position|exact exception_instruction_8157_safe|exact exception_instruction_8157_nonregister| |reflexivity|exact Step].
 unfold exception_instruction_8157_expr. cbn [eval_hfexpr_with_memory eval_href_with_memory]. exact Source.
Qed.
Definition exception_instruction_8246_expr : hfexpr VarOrder.T := (@Eref VarOrder.T (@Eid VarOrder.T 8157)).
Definition exception_instruction_8246_tail := match straight_drop 8753 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma exception_instruction_8246_position : straight_drop 8752 flat_statements = Some (@Qcons VarOrder.T (@Snode VarOrder.T 8246 exception_instruction_8246_expr) exception_instruction_8246_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma exception_instruction_8246_safe : formal_typed_suffix_safe flat_memories 8246 exception_instruction_8246_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma exception_instruction_8246_nonregister : has_register 8246 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem exception_instruction_8246_value invalid old current result bits :
 VM.find 8157 old = Some (Gval (Fuint 32) bits) ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 8246 result = Some (Gval (Fuint 32) bits).
Proof.
 intros Source Step. eapply formal_combinational_known_node;
 [exact exception_instruction_8246_position|exact exception_instruction_8246_safe|exact exception_instruction_8246_nonregister| |reflexivity|exact Step].
 unfold exception_instruction_8246_expr. cbn [eval_hfexpr_with_memory eval_href_with_memory]. exact Source.
Qed.
Print Assumptions exception_instruction_8246_value.
