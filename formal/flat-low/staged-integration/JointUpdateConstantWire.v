Require Import FormalDeclaredConnection FormalDeclaredConstantConnection ScalarNodeFrames FormalStatementSegments FormalTypedNodeFrames FormalTypedNodeEquation CoreSocModel ComparisonNodes RegisterInvariants.
From Coq Require Import ZArith.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory FormalInitialization.
Local Open Scope N_scope.
Definition joint_constant_wire_decl_25 := match straight_drop 3 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition joint_constant_wire_tail_25 := match straight_drop 10095 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition joint_constant_wire_mid_25 := take_statements 10091 joint_constant_wire_decl_25.
Lemma joint_constant_wire_position_25 : straight_drop 2 flat_statements = Some (@Qcons VarOrder.T (@Swire VarOrder.T 25 (Gtyp (Fuint 1))) joint_constant_wire_decl_25).
Proof. vm_compute. reflexivity. Qed.
Lemma joint_constant_wire_split_25 : joint_constant_wire_decl_25 = statement_append joint_constant_wire_mid_25 (@Qcons VarOrder.T (@Sfcnct VarOrder.T (@Eid VarOrder.T 25) (@Econst VarOrder.T (Fuint 1) [::false])) joint_constant_wire_tail_25).
Proof. vm_compute. reflexivity. Qed.
Lemma joint_constant_wire_straight_25 : straight_statements joint_constant_wire_mid_25.
Proof. vm_compute. exact I. Qed.
Lemma joint_constant_wire_mid_safe_25 : formal_typed_suffix_safe flat_memories 25 joint_constant_wire_mid_25.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma joint_constant_wire_tail_safe_25 : formal_typed_suffix_safe flat_memories 25 joint_constant_wire_tail_25.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma joint_constant_wire_nonregister_25 : has_register 25 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem joint_constant_wire_25_output invalid old current result :
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 25 result = Some (Gval (Fuint 1) [::false]).
Proof.
 intro Step.
 exact (declared_constant_connection_value 2 flat_statements joint_constant_wire_decl_25 joint_constant_wire_mid_25 joint_constant_wire_tail_25
 25 (Fuint 1) [::false] 1 (Gval (Fuint 1) [::false]) (Gval (Fuint 1) [::false]) invalid flat_memories old current result
 joint_constant_wire_position_25 joint_constant_wire_split_25 joint_constant_wire_straight_25 joint_constant_wire_mid_safe_25 joint_constant_wire_tail_safe_25
 joint_constant_wire_nonregister_25 (Logic.eq_refl _) (Logic.eq_refl _) Step).
Qed.
Print Assumptions joint_constant_wire_25_output.
