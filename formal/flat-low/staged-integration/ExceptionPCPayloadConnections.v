Require Import CoreSocModel ComparisonNodes RegisterInvariants ScalarNodeFrames FormalTypedNodeFrames FormalTypedNodeEquation FormalDeclaredConnection FormalStatementSegments.
From Coq Require Import ZArith.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Definition exception_pc_121_decl := match straight_drop 99 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition exception_pc_121_tail := match straight_drop 8789 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition exception_pc_121_mid := take_statements 8689 exception_pc_121_decl.
Lemma exception_pc_121_position : straight_drop 98 flat_statements = Some (@Qcons VarOrder.T (@Swire VarOrder.T 121 (Gtyp (Fuint 32))) exception_pc_121_decl).
Proof. vm_compute. reflexivity. Qed.
Lemma exception_pc_121_split : exception_pc_121_decl = statement_append exception_pc_121_mid (@Qcons VarOrder.T (@Sfcnct VarOrder.T (@Eid VarOrder.T 121) (@Eref VarOrder.T (@Eid VarOrder.T 7751))) exception_pc_121_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma exception_pc_121_straight : straight_statements exception_pc_121_mid.
Proof. vm_compute. exact I. Qed.
Lemma exception_pc_121_mid_safe : formal_typed_suffix_safe flat_memories 121 exception_pc_121_mid.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma exception_pc_121_tail_safe : formal_typed_suffix_safe flat_memories 121 exception_pc_121_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma exception_pc_121_nonregister : has_register 121 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem exception_pc_121_value invalid old current result source value :
 VM.find 7751 old = Some source ->
 adapt_hvalue_as_type source (Gtyp (Fuint 32)) = Some value ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 121 result = Some value.
Proof.
 intros Source Adapt Step.
 exact (declared_connection_value 98 flat_statements exception_pc_121_decl exception_pc_121_mid exception_pc_121_tail
 121 7751 32 source value invalid flat_memories old current result
 exception_pc_121_position exception_pc_121_split exception_pc_121_straight exception_pc_121_mid_safe exception_pc_121_tail_safe exception_pc_121_nonregister
 (Logic.eq_refl _) Source Adapt Step).
Qed.
Definition exception_pc_1749_decl := match straight_drop 1829 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition exception_pc_1749_tail := match straight_drop 7997 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition exception_pc_1749_mid := take_statements 6167 exception_pc_1749_decl.
Lemma exception_pc_1749_position : straight_drop 1828 flat_statements = Some (@Qcons VarOrder.T (@Swire VarOrder.T 1749 (Gtyp (Fuint 32))) exception_pc_1749_decl).
Proof. vm_compute. reflexivity. Qed.
Lemma exception_pc_1749_split : exception_pc_1749_decl = statement_append exception_pc_1749_mid (@Qcons VarOrder.T (@Sfcnct VarOrder.T (@Eid VarOrder.T 1749) (@Eref VarOrder.T (@Eid VarOrder.T 7331))) exception_pc_1749_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma exception_pc_1749_straight : straight_statements exception_pc_1749_mid.
Proof. vm_compute. exact I. Qed.
Lemma exception_pc_1749_mid_safe : formal_typed_suffix_safe flat_memories 1749 exception_pc_1749_mid.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma exception_pc_1749_tail_safe : formal_typed_suffix_safe flat_memories 1749 exception_pc_1749_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma exception_pc_1749_nonregister : has_register 1749 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem exception_pc_1749_value invalid old current result source value :
 VM.find 7331 old = Some source ->
 adapt_hvalue_as_type source (Gtyp (Fuint 32)) = Some value ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 1749 result = Some value.
Proof.
 intros Source Adapt Step.
 exact (declared_connection_value 1828 flat_statements exception_pc_1749_decl exception_pc_1749_mid exception_pc_1749_tail
 1749 7331 32 source value invalid flat_memories old current result
 exception_pc_1749_position exception_pc_1749_split exception_pc_1749_straight exception_pc_1749_mid_safe exception_pc_1749_tail_safe exception_pc_1749_nonregister
 (Logic.eq_refl _) Source Adapt Step).
Qed.
Print Assumptions exception_pc_1749_value.
