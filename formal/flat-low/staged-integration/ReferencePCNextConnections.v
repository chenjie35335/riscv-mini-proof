Require Import CoreSocModel ComparisonNodes RegisterInvariants ScalarNodeFrames FormalTypedNodeFrames FormalTypedNodeEquation FormalDeclaredConnection FormalStatementSegments.
From Coq Require Import ZArith.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Definition exception_pc_1819_decl := match straight_drop 1899 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition exception_pc_1819_tail := match straight_drop 7390 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition exception_pc_1819_mid := take_statements 5490 exception_pc_1819_decl.
Lemma exception_pc_1819_position : straight_drop 1898 flat_statements = Some (@Qcons VarOrder.T (@Swire VarOrder.T 1819 (Gtyp (Fuint 32))) exception_pc_1819_decl).
Proof. vm_compute. reflexivity. Qed.
Lemma exception_pc_1819_split : exception_pc_1819_decl = statement_append exception_pc_1819_mid (@Qcons VarOrder.T (@Sfcnct VarOrder.T (@Eid VarOrder.T 1819) (@Eref VarOrder.T (@Eid VarOrder.T 7149))) exception_pc_1819_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma exception_pc_1819_straight : straight_statements exception_pc_1819_mid.
Proof. vm_compute. exact I. Qed.
Lemma exception_pc_1819_mid_safe : formal_typed_suffix_safe flat_memories 1819 exception_pc_1819_mid.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma exception_pc_1819_tail_safe : formal_typed_suffix_safe flat_memories 1819 exception_pc_1819_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma exception_pc_1819_nonregister : has_register 1819 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem exception_pc_1819_value invalid old current result source value :
 VM.find 7149 old = Some source ->
 adapt_hvalue_as_type source (Gtyp (Fuint 32)) = Some value ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 1819 result = Some value.
Proof.
 intros Source Adapt Step.
 exact (declared_connection_value 1898 flat_statements exception_pc_1819_decl exception_pc_1819_mid exception_pc_1819_tail
 1819 7149 32 source value invalid flat_memories old current result
 exception_pc_1819_position exception_pc_1819_split exception_pc_1819_straight exception_pc_1819_mid_safe exception_pc_1819_tail_safe exception_pc_1819_nonregister
 (Logic.eq_refl _) Source Adapt Step).
Qed.
Print Assumptions exception_pc_1819_value.
