Require Import FormalDeclaredConcreteUnaryConnection.
From firrtl Require Import Firrtl_with_implicit_widths.
Require Import CoreSocModel ComparisonNodes FormalDeclaredConnection FormalDeclaredConcreteConnection ScalarNodeFrames FormalStatementSegments FormalTypedNodeFrames FormalTypedNodeEquation RegisterInvariants.
From Coq Require Import ZArith.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Definition data_address_connection_78_decl := match straight_drop 56 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition data_address_connection_78_tail := match straight_drop 8762 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition data_address_connection_78_mid := take_statements 8705 data_address_connection_78_decl.
Lemma data_address_connection_78_position : straight_drop 55 flat_statements = Some (@Qcons VarOrder.T (@Swire VarOrder.T 78 (Gtyp (Fuint 32))) data_address_connection_78_decl).
Proof. vm_compute. reflexivity. Qed.
Lemma data_address_connection_78_split : data_address_connection_78_decl = statement_append data_address_connection_78_mid (@Qcons VarOrder.T (@Sfcnct VarOrder.T (@Eid VarOrder.T 78) (@Eprim_unop VarOrder.T (Uextr 31 0) (@Eref VarOrder.T (@Eid VarOrder.T 7826)))) data_address_connection_78_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma data_address_connection_78_straight : straight_statements data_address_connection_78_mid.
Proof. vm_compute. exact I. Qed.
Lemma data_address_connection_78_mid_safe : formal_typed_suffix_safe flat_memories 78 data_address_connection_78_mid.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma data_address_connection_78_tail_safe : formal_typed_suffix_safe flat_memories 78 data_address_connection_78_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma data_address_connection_78_nonregister : has_register 78 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem data_address_connection_78_output invalid old current result :
 (exists ground bits, VM.find 7826 old = Some (Gval ground bits)) ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 exists bits, VM.find 78 result = Some (Gval (Fuint 32) bits).
Proof.
 intros [ground [bits Source]] Step.
 exact (declared_unary_connection_concrete 55 flat_statements data_address_connection_78_decl data_address_connection_78_mid data_address_connection_78_tail
 78 7826 (Uextr 31 0) 32 ground bits invalid flat_memories old current result
 data_address_connection_78_position data_address_connection_78_split data_address_connection_78_straight data_address_connection_78_mid_safe data_address_connection_78_tail_safe
 data_address_connection_78_nonregister (Logic.eq_refl _) Source Step).
Qed.
Print Assumptions data_address_connection_78_output.
