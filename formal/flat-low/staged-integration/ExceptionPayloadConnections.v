Require Import CoreSocModel ComparisonNodes RegisterInvariants ScalarNodeFrames FormalTypedNodeFrames FormalTypedNodeEquation FormalDeclaredConnection FormalStatementSegments.
From Coq Require Import ZArith.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Definition exception_instruction_1396_decl := match straight_drop 1476 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition exception_instruction_1396_tail := match straight_drop 8885 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition exception_instruction_1396_mid := take_statements 7408 exception_instruction_1396_decl.
Lemma exception_instruction_1396_position : straight_drop 1475 flat_statements = Some (@Qcons VarOrder.T (@Swire VarOrder.T 1396 (Gtyp (Fuint 32))) exception_instruction_1396_decl).
Proof. vm_compute. reflexivity. Qed.
Lemma exception_instruction_1396_split : exception_instruction_1396_decl = statement_append exception_instruction_1396_mid (@Qcons VarOrder.T (@Sfcnct VarOrder.T (@Eid VarOrder.T 1396) (@Eref VarOrder.T (@Eid VarOrder.T 7750))) exception_instruction_1396_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma exception_instruction_1396_straight : straight_statements exception_instruction_1396_mid.
Proof. vm_compute. exact I. Qed.
Lemma exception_instruction_1396_mid_safe : formal_typed_suffix_safe flat_memories 1396 exception_instruction_1396_mid.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma exception_instruction_1396_tail_safe : formal_typed_suffix_safe flat_memories 1396 exception_instruction_1396_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma exception_instruction_1396_nonregister : has_register 1396 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem exception_instruction_1396_value invalid old current result source value :
 VM.find 7750 old = Some source ->
 adapt_hvalue_as_type source (Gtyp (Fuint 32)) = Some value ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 1396 result = Some value.
Proof.
 intros Source Adapt Step.
 exact (declared_connection_value 1475 flat_statements exception_instruction_1396_decl exception_instruction_1396_mid exception_instruction_1396_tail
 1396 7750 32 source value invalid flat_memories old current result
 exception_instruction_1396_position exception_instruction_1396_split exception_instruction_1396_straight exception_instruction_1396_mid_safe exception_instruction_1396_tail_safe exception_instruction_1396_nonregister
 (Logic.eq_refl _) Source Adapt Step).
Qed.
Definition exception_instruction_1516_decl := match straight_drop 1596 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition exception_instruction_1516_tail := match straight_drop 8220 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition exception_instruction_1516_mid := take_statements 6623 exception_instruction_1516_decl.
Lemma exception_instruction_1516_position : straight_drop 1595 flat_statements = Some (@Qcons VarOrder.T (@Swire VarOrder.T 1516 (Gtyp (Fuint 32))) exception_instruction_1516_decl).
Proof. vm_compute. reflexivity. Qed.
Lemma exception_instruction_1516_split : exception_instruction_1516_decl = statement_append exception_instruction_1516_mid (@Qcons VarOrder.T (@Sfcnct VarOrder.T (@Eid VarOrder.T 1516) (@Eref VarOrder.T (@Eid VarOrder.T 1396))) exception_instruction_1516_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma exception_instruction_1516_straight : straight_statements exception_instruction_1516_mid.
Proof. vm_compute. exact I. Qed.
Lemma exception_instruction_1516_mid_safe : formal_typed_suffix_safe flat_memories 1516 exception_instruction_1516_mid.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma exception_instruction_1516_tail_safe : formal_typed_suffix_safe flat_memories 1516 exception_instruction_1516_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma exception_instruction_1516_nonregister : has_register 1516 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem exception_instruction_1516_value invalid old current result source value :
 VM.find 1396 old = Some source ->
 adapt_hvalue_as_type source (Gtyp (Fuint 32)) = Some value ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 1516 result = Some value.
Proof.
 intros Source Adapt Step.
 exact (declared_connection_value 1595 flat_statements exception_instruction_1516_decl exception_instruction_1516_mid exception_instruction_1516_tail
 1516 1396 32 source value invalid flat_memories old current result
 exception_instruction_1516_position exception_instruction_1516_split exception_instruction_1516_straight exception_instruction_1516_mid_safe exception_instruction_1516_tail_safe exception_instruction_1516_nonregister
 (Logic.eq_refl _) Source Adapt Step).
Qed.
Definition exception_instruction_1706_decl := match straight_drop 1786 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition exception_instruction_1706_tail := match straight_drop 7962 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition exception_instruction_1706_mid := take_statements 6175 exception_instruction_1706_decl.
Lemma exception_instruction_1706_position : straight_drop 1785 flat_statements = Some (@Qcons VarOrder.T (@Swire VarOrder.T 1706 (Gtyp (Fuint 32))) exception_instruction_1706_decl).
Proof. vm_compute. reflexivity. Qed.
Lemma exception_instruction_1706_split : exception_instruction_1706_decl = statement_append exception_instruction_1706_mid (@Qcons VarOrder.T (@Sfcnct VarOrder.T (@Eid VarOrder.T 1706) (@Eref VarOrder.T (@Eid VarOrder.T 1516))) exception_instruction_1706_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma exception_instruction_1706_straight : straight_statements exception_instruction_1706_mid.
Proof. vm_compute. exact I. Qed.
Lemma exception_instruction_1706_mid_safe : formal_typed_suffix_safe flat_memories 1706 exception_instruction_1706_mid.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma exception_instruction_1706_tail_safe : formal_typed_suffix_safe flat_memories 1706 exception_instruction_1706_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma exception_instruction_1706_nonregister : has_register 1706 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem exception_instruction_1706_value invalid old current result source value :
 VM.find 1516 old = Some source ->
 adapt_hvalue_as_type source (Gtyp (Fuint 32)) = Some value ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 1706 result = Some value.
Proof.
 intros Source Adapt Step.
 exact (declared_connection_value 1785 flat_statements exception_instruction_1706_decl exception_instruction_1706_mid exception_instruction_1706_tail
 1706 1516 32 source value invalid flat_memories old current result
 exception_instruction_1706_position exception_instruction_1706_split exception_instruction_1706_straight exception_instruction_1706_mid_safe exception_instruction_1706_tail_safe exception_instruction_1706_nonregister
 (Logic.eq_refl _) Source Adapt Step).
Qed.
Print Assumptions exception_instruction_1706_value.
