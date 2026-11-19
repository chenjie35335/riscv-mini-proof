Require Import CoreSocModel ComparisonNodes RegisterInvariants ScalarNodeFrames FormalTypedNodeFrames FormalTypedNodeEquation FormalDeclaredConnection FormalStatementSegments.
From Coq Require Import ZArith.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Definition interrupt_zero : seq bool := nseq 32 false.
Definition interrupt_774_expr : hfexpr VarOrder.T := (@Econst VarOrder.T (Fuint 32) [::false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false]).
Definition interrupt_774_tail := match straight_drop 752 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma interrupt_774_position : straight_drop 751 flat_statements = Some (@Qcons VarOrder.T (@Snode VarOrder.T 774 interrupt_774_expr) interrupt_774_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma interrupt_774_safe : formal_typed_suffix_safe flat_memories 774 interrupt_774_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma interrupt_774_nonregister : has_register 774 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem interrupt_774_zero invalid old current result :
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 774 result = Some (Gval (Fuint 32) interrupt_zero).
Proof.
 intros Step.
 eapply formal_combinational_known_node;
 [exact interrupt_774_position|exact interrupt_774_safe|exact interrupt_774_nonregister| |reflexivity|exact Step].
 unfold interrupt_774_expr. cbn [eval_hfexpr_with_memory eval_href_with_memory].
 reflexivity.
Qed.
Definition interrupt_7203_expr : hfexpr VarOrder.T := (@Econst VarOrder.T (Fuint 32) [::false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false]).
Definition interrupt_7203_tail := match straight_drop 7283 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma interrupt_7203_position : straight_drop 7282 flat_statements = Some (@Qcons VarOrder.T (@Snode VarOrder.T 7203 interrupt_7203_expr) interrupt_7203_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma interrupt_7203_safe : formal_typed_suffix_safe flat_memories 7203 interrupt_7203_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma interrupt_7203_nonregister : has_register 7203 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem interrupt_7203_zero invalid old current result :
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 7203 result = Some (Gval (Fuint 32) interrupt_zero).
Proof.
 intros Step.
 eapply formal_combinational_known_node;
 [exact interrupt_7203_position|exact interrupt_7203_safe|exact interrupt_7203_nonregister| |reflexivity|exact Step].
 unfold interrupt_7203_expr. cbn [eval_hfexpr_with_memory eval_href_with_memory].
 reflexivity.
Qed.
Definition interrupt_7204_expr : hfexpr VarOrder.T := (@Eref VarOrder.T (@Eid VarOrder.T 7203)).
Definition interrupt_7204_tail := match straight_drop 7284 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma interrupt_7204_position : straight_drop 7283 flat_statements = Some (@Qcons VarOrder.T (@Snode VarOrder.T 7204 interrupt_7204_expr) interrupt_7204_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma interrupt_7204_safe : formal_typed_suffix_safe flat_memories 7204 interrupt_7204_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma interrupt_7204_nonregister : has_register 7204 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem interrupt_7204_zero invalid old current result :
 VM.find 7203 old = Some (Gval (Fuint 32) interrupt_zero) ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 7204 result = Some (Gval (Fuint 32) interrupt_zero).
Proof.
 intros Source Step.
 eapply formal_combinational_known_node;
 [exact interrupt_7204_position|exact interrupt_7204_safe|exact interrupt_7204_nonregister| |reflexivity|exact Step].
 unfold interrupt_7204_expr. cbn [eval_hfexpr_with_memory eval_href_with_memory].
 exact Source.
Qed.
Definition interrupt_8154_expr : hfexpr VarOrder.T := (@Eref VarOrder.T (@Eid VarOrder.T 135)).
Definition interrupt_8154_tail := match straight_drop 8661 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma interrupt_8154_position : straight_drop 8660 flat_statements = Some (@Qcons VarOrder.T (@Snode VarOrder.T 8154 interrupt_8154_expr) interrupt_8154_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma interrupt_8154_safe : formal_typed_suffix_safe flat_memories 8154 interrupt_8154_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma interrupt_8154_nonregister : has_register 8154 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem interrupt_8154_zero invalid old current result :
 VM.find 135 old = Some (Gval (Fuint 32) interrupt_zero) ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 8154 result = Some (Gval (Fuint 32) interrupt_zero).
Proof.
 intros Source Step.
 eapply formal_combinational_known_node;
 [exact interrupt_8154_position|exact interrupt_8154_safe|exact interrupt_8154_nonregister| |reflexivity|exact Step].
 unfold interrupt_8154_expr. cbn [eval_hfexpr_with_memory eval_href_with_memory].
 exact Source.
Qed.
Definition interrupt_8243_expr : hfexpr VarOrder.T := (@Eref VarOrder.T (@Eid VarOrder.T 8154)).
Definition interrupt_8243_tail := match straight_drop 8750 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma interrupt_8243_position : straight_drop 8749 flat_statements = Some (@Qcons VarOrder.T (@Snode VarOrder.T 8243 interrupt_8243_expr) interrupt_8243_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma interrupt_8243_safe : formal_typed_suffix_safe flat_memories 8243 interrupt_8243_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma interrupt_8243_nonregister : has_register 8243 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem interrupt_8243_zero invalid old current result :
 VM.find 8154 old = Some (Gval (Fuint 32) interrupt_zero) ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 8243 result = Some (Gval (Fuint 32) interrupt_zero).
Proof.
 intros Source Step.
 eapply formal_combinational_known_node;
 [exact interrupt_8243_position|exact interrupt_8243_safe|exact interrupt_8243_nonregister| |reflexivity|exact Step].
 unfold interrupt_8243_expr. cbn [eval_hfexpr_with_memory eval_href_with_memory].
 exact Source.
Qed.
Print Assumptions interrupt_8243_zero.
