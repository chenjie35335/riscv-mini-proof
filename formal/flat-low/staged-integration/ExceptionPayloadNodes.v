Require Import CoreSocModel ComparisonNodes RegisterInvariants ScalarNodeFrames FormalTypedNodeFrames FormalTypedNodeEquation FormalDeclaredConnection FormalStatementSegments.
From Coq Require Import ZArith.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Definition exception_instruction_1884_expr : hfexpr VarOrder.T := (@Eref VarOrder.T (@Eid VarOrder.T 1883)).
Definition exception_instruction_1884_tail := match straight_drop 1964 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma exception_instruction_1884_position : straight_drop 1963 flat_statements = Some (@Qcons VarOrder.T (@Snode VarOrder.T 1884 exception_instruction_1884_expr) exception_instruction_1884_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma exception_instruction_1884_safe : formal_typed_suffix_safe flat_memories 1884 exception_instruction_1884_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma exception_instruction_1884_nonregister : has_register 1884 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem exception_instruction_1884_value invalid old current result bits :
 VM.find 1883 old = Some (Gval (Fuint 32) bits) ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 1884 result = Some (Gval (Fuint 32) bits).
Proof.
 intros Source Step. eapply formal_combinational_known_node;
 [exact exception_instruction_1884_position|exact exception_instruction_1884_safe|exact exception_instruction_1884_nonregister| |reflexivity|exact Step].
 unfold exception_instruction_1884_expr. cbn [eval_hfexpr_with_memory eval_href_with_memory]. exact Source.
Qed.
Print Assumptions exception_instruction_1884_value.
