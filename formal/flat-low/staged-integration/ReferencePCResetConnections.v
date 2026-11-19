Require Import CoreSocModel ComparisonNodes RegisterInvariants ScalarNodeFrames FormalTypedNodeFrames FormalTypedNodeEquation FormalDeclaredConnection FormalStatementSegments.
From Coq Require Import ZArith.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Definition exception_pc_1515_decl := match straight_drop 1595 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition exception_pc_1515_tail := match straight_drop 8219 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition exception_pc_1515_mid := take_statements 6623 exception_pc_1515_decl.
Lemma exception_pc_1515_position : straight_drop 1594 flat_statements = Some (@Qcons VarOrder.T (@Swire VarOrder.T 1515 (Gtyp (Fuint 1))) exception_pc_1515_decl).
Proof. vm_compute. reflexivity. Qed.
Lemma exception_pc_1515_split : exception_pc_1515_decl = statement_append exception_pc_1515_mid (@Qcons VarOrder.T (@Sfcnct VarOrder.T (@Eid VarOrder.T 1515) (@Eref VarOrder.T (@Eid VarOrder.T 1394))) exception_pc_1515_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma exception_pc_1515_straight : straight_statements exception_pc_1515_mid.
Proof. vm_compute. exact I. Qed.
Lemma exception_pc_1515_mid_safe : formal_typed_suffix_safe flat_memories 1515 exception_pc_1515_mid.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma exception_pc_1515_tail_safe : formal_typed_suffix_safe flat_memories 1515 exception_pc_1515_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma exception_pc_1515_nonregister : has_register 1515 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem exception_pc_1515_value invalid old current result source value :
 VM.find 1394 old = Some source ->
 adapt_hvalue_as_type source (Gtyp (Fuint 1)) = Some value ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 1515 result = Some value.
Proof.
 intros Source Adapt Step.
 exact (declared_connection_value 1594 flat_statements exception_pc_1515_decl exception_pc_1515_mid exception_pc_1515_tail
 1515 1394 1 source value invalid flat_memories old current result
 exception_pc_1515_position exception_pc_1515_split exception_pc_1515_straight exception_pc_1515_mid_safe exception_pc_1515_tail_safe exception_pc_1515_nonregister
 (Logic.eq_refl _) Source Adapt Step).
Qed.
Print Assumptions exception_pc_1515_value.
