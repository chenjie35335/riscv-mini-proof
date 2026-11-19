Require Import CoreSocModel ComparisonNodes RegisterInvariants ScalarNodeFrames FormalTypedNodeFrames FormalTypedNodeEquation FormalDeclaredConnection FormalStatementSegments.
From Coq Require Import ZArith.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Definition exception_event_773_expr : hfexpr VarOrder.T := (@Eref VarOrder.T (@Eid VarOrder.T 128)).
Definition exception_event_773_tail := match straight_drop 751 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma exception_event_773_position : straight_drop 750 flat_statements = Some (@Qcons VarOrder.T (@Snode VarOrder.T 773 exception_event_773_expr) exception_event_773_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma exception_event_773_safe : formal_typed_suffix_safe flat_memories 773 exception_event_773_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma exception_event_773_nonregister : has_register 773 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem exception_event_773_value invalid old current result bits :
 VM.find 128 old = Some (Gval (Fuint 1) bits) ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 773 result = Some (Gval (Fuint 1) bits).
Proof.
 intros Source Step. eapply formal_combinational_known_node;
 [exact exception_event_773_position|exact exception_event_773_safe|exact exception_event_773_nonregister| |reflexivity|exact Step].
 unfold exception_event_773_expr. cbn [eval_hfexpr_with_memory eval_href_with_memory]. exact Source.
Qed.
Definition exception_event_8153_expr : hfexpr VarOrder.T := (@Eref VarOrder.T (@Eid VarOrder.T 134)).
Definition exception_event_8153_tail := match straight_drop 8660 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma exception_event_8153_position : straight_drop 8659 flat_statements = Some (@Qcons VarOrder.T (@Snode VarOrder.T 8153 exception_event_8153_expr) exception_event_8153_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma exception_event_8153_safe : formal_typed_suffix_safe flat_memories 8153 exception_event_8153_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma exception_event_8153_nonregister : has_register 8153 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem exception_event_8153_value invalid old current result bits :
 VM.find 134 old = Some (Gval (Fuint 1) bits) ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 8153 result = Some (Gval (Fuint 1) bits).
Proof.
 intros Source Step. eapply formal_combinational_known_node;
 [exact exception_event_8153_position|exact exception_event_8153_safe|exact exception_event_8153_nonregister| |reflexivity|exact Step].
 unfold exception_event_8153_expr. cbn [eval_hfexpr_with_memory eval_href_with_memory]. exact Source.
Qed.
Definition exception_event_8242_expr : hfexpr VarOrder.T := (@Eref VarOrder.T (@Eid VarOrder.T 8153)).
Definition exception_event_8242_tail := match straight_drop 8749 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma exception_event_8242_position : straight_drop 8748 flat_statements = Some (@Qcons VarOrder.T (@Snode VarOrder.T 8242 exception_event_8242_expr) exception_event_8242_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma exception_event_8242_safe : formal_typed_suffix_safe flat_memories 8242 exception_event_8242_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma exception_event_8242_nonregister : has_register 8242 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem exception_event_8242_value invalid old current result bits :
 VM.find 8153 old = Some (Gval (Fuint 1) bits) ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 8242 result = Some (Gval (Fuint 1) bits).
Proof.
 intros Source Step. eapply formal_combinational_known_node;
 [exact exception_event_8242_position|exact exception_event_8242_safe|exact exception_event_8242_nonregister| |reflexivity|exact Step].
 unfold exception_event_8242_expr. cbn [eval_hfexpr_with_memory eval_href_with_memory]. exact Source.
Qed.
Print Assumptions exception_event_8242_value.
