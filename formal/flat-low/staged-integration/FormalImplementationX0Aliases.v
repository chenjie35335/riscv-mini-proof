Require Import RegisterInvariants CoreSocModel ComparisonNodes ScalarNodeFrames FormalTypedNodeFrames FormalTypedNodeEquation.
From Coq Require Import ZArith.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths Firrtl_with_implicit_widths HiEnv_with_implicit_widths
 HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Definition expr_1117 := (@Eref VarOrder.T (@Eid VarOrder.T 1053)).
Definition tail_1117 := match straight_drop 1127 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma position_1117 : straight_drop 1126 flat_statements = Some (@Qcons VarOrder.T (@Snode VarOrder.T 1117 expr_1117) tail_1117).
Proof. vm_compute. reflexivity. Qed.
Lemma suffix_1117 : formal_typed_suffix_safe flat_memories 1117 tail_1117.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma nonregister_1117 : has_register 1117 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem node_1117_transfer invalid old current result width value :
 VM.find 1053 old = Some value -> type_of_val value = Gtyp (Fuint width) ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 1117 result = Some value.
Proof. intros Source Typed Step. eapply formal_combinational_known_node;
 [exact position_1117|exact suffix_1117|exact nonregister_1117| |exact Typed|exact Step].
 exact Source. Qed.
Definition expr_8041 := (@Eref VarOrder.T (@Eid VarOrder.T 819)).
Definition tail_8041 := match straight_drop 8548 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma position_8041 : straight_drop 8547 flat_statements = Some (@Qcons VarOrder.T (@Snode VarOrder.T 8041 expr_8041) tail_8041).
Proof. vm_compute. reflexivity. Qed.
Lemma suffix_8041 : formal_typed_suffix_safe flat_memories 8041 tail_8041.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma nonregister_8041 : has_register 8041 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem node_8041_transfer invalid old current result width value :
 VM.find 819 old = Some value -> type_of_val value = Gtyp (Fuint width) ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 8041 result = Some value.
Proof. intros Source Typed Step. eapply formal_combinational_known_node;
 [exact position_8041|exact suffix_8041|exact nonregister_8041| |exact Typed|exact Step].
 exact Source. Qed.
Definition expr_8166 := (@Eref VarOrder.T (@Eid VarOrder.T 8041)).
Definition tail_8166 := match straight_drop 8673 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma position_8166 : straight_drop 8672 flat_statements = Some (@Qcons VarOrder.T (@Snode VarOrder.T 8166 expr_8166) tail_8166).
Proof. vm_compute. reflexivity. Qed.
Lemma suffix_8166 : formal_typed_suffix_safe flat_memories 8166 tail_8166.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma nonregister_8166 : has_register 8166 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem node_8166_transfer invalid old current result width value :
 VM.find 8041 old = Some value -> type_of_val value = Gtyp (Fuint width) ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 8166 result = Some value.
Proof. intros Source Typed Step. eapply formal_combinational_known_node;
 [exact position_8166|exact suffix_8166|exact nonregister_8166| |exact Typed|exact Step].
 exact Source. Qed.
Print Assumptions node_8166_transfer.
