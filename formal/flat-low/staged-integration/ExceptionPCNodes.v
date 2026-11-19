Require Import CoreSocModel ComparisonNodes RegisterInvariants ScalarNodeFrames FormalTypedNodeFrames FormalTypedNodeEquation FormalDeclaredConnection FormalStatementSegments.
From Coq Require Import ZArith.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Definition exception_pc_776_expr : hfexpr VarOrder.T := (@Eref VarOrder.T (@Eid VarOrder.T 772)).
Definition exception_pc_776_tail := match straight_drop 754 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma exception_pc_776_position : straight_drop 753 flat_statements = Some (@Qcons VarOrder.T (@Snode VarOrder.T 776 exception_pc_776_expr) exception_pc_776_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma exception_pc_776_safe : formal_typed_suffix_safe flat_memories 776 exception_pc_776_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma exception_pc_776_nonregister : has_register 776 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem exception_pc_776_value invalid old current result bits :
 VM.find 772 old = Some (Gval (Fuint 32) bits) ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 776 result = Some (Gval (Fuint 32) bits).
Proof.
 intros Source Step. eapply formal_combinational_known_node;
 [exact exception_pc_776_position|exact exception_pc_776_safe|exact exception_pc_776_nonregister| |reflexivity|exact Step].
 unfold exception_pc_776_expr. cbn [eval_hfexpr_with_memory eval_href_with_memory]. exact Source.
Qed.
Definition exception_pc_7206_expr : hfexpr VarOrder.T := (@Eref VarOrder.T (@Eid VarOrder.T 7119)).
Definition exception_pc_7206_tail := match straight_drop 7286 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma exception_pc_7206_position : straight_drop 7285 flat_statements = Some (@Qcons VarOrder.T (@Snode VarOrder.T 7206 exception_pc_7206_expr) exception_pc_7206_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma exception_pc_7206_safe : formal_typed_suffix_safe flat_memories 7206 exception_pc_7206_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma exception_pc_7206_nonregister : has_register 7206 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem exception_pc_7206_value invalid old current result bits :
 VM.find 7119 old = Some (Gval (Fuint 32) bits) ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 7206 result = Some (Gval (Fuint 32) bits).
Proof.
 intros Source Step. eapply formal_combinational_known_node;
 [exact exception_pc_7206_position|exact exception_pc_7206_safe|exact exception_pc_7206_nonregister| |reflexivity|exact Step].
 unfold exception_pc_7206_expr. cbn [eval_hfexpr_with_memory eval_href_with_memory]. exact Source.
Qed.
Definition exception_pc_8156_expr : hfexpr VarOrder.T := (@Eref VarOrder.T (@Eid VarOrder.T 137)).
Definition exception_pc_8156_tail := match straight_drop 8663 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma exception_pc_8156_position : straight_drop 8662 flat_statements = Some (@Qcons VarOrder.T (@Snode VarOrder.T 8156 exception_pc_8156_expr) exception_pc_8156_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma exception_pc_8156_safe : formal_typed_suffix_safe flat_memories 8156 exception_pc_8156_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma exception_pc_8156_nonregister : has_register 8156 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem exception_pc_8156_value invalid old current result bits :
 VM.find 137 old = Some (Gval (Fuint 32) bits) ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 8156 result = Some (Gval (Fuint 32) bits).
Proof.
 intros Source Step. eapply formal_combinational_known_node;
 [exact exception_pc_8156_position|exact exception_pc_8156_safe|exact exception_pc_8156_nonregister| |reflexivity|exact Step].
 unfold exception_pc_8156_expr. cbn [eval_hfexpr_with_memory eval_href_with_memory]. exact Source.
Qed.
Definition exception_pc_8245_expr : hfexpr VarOrder.T := (@Eref VarOrder.T (@Eid VarOrder.T 8156)).
Definition exception_pc_8245_tail := match straight_drop 8752 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma exception_pc_8245_position : straight_drop 8751 flat_statements = Some (@Qcons VarOrder.T (@Snode VarOrder.T 8245 exception_pc_8245_expr) exception_pc_8245_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma exception_pc_8245_safe : formal_typed_suffix_safe flat_memories 8245 exception_pc_8245_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma exception_pc_8245_nonregister : has_register 8245 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem exception_pc_8245_value invalid old current result bits :
 VM.find 8156 old = Some (Gval (Fuint 32) bits) ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 8245 result = Some (Gval (Fuint 32) bits).
Proof.
 intros Source Step. eapply formal_combinational_known_node;
 [exact exception_pc_8245_position|exact exception_pc_8245_safe|exact exception_pc_8245_nonregister| |reflexivity|exact Step].
 unfold exception_pc_8245_expr. cbn [eval_hfexpr_with_memory eval_href_with_memory]. exact Source.
Qed.
Print Assumptions exception_pc_8245_value.
