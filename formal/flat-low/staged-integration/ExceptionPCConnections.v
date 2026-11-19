Require Import CoreSocModel ComparisonNodes RegisterInvariants ScalarNodeFrames FormalTypedNodeFrames FormalTypedNodeEquation FormalDeclaredConnection FormalStatementSegments.
From Coq Require Import ZArith.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Definition exception_pc_137_decl := match straight_drop 115 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition exception_pc_137_tail := match straight_drop 764 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition exception_pc_137_mid := take_statements 648 exception_pc_137_decl.
Lemma exception_pc_137_position : straight_drop 114 flat_statements = Some (@Qcons VarOrder.T (@Swire VarOrder.T 137 (Gtyp (Fuint 32))) exception_pc_137_decl).
Proof. vm_compute. reflexivity. Qed.
Lemma exception_pc_137_split : exception_pc_137_decl = statement_append exception_pc_137_mid (@Qcons VarOrder.T (@Sfcnct VarOrder.T (@Eid VarOrder.T 137) (@Eref VarOrder.T (@Eid VarOrder.T 776))) exception_pc_137_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma exception_pc_137_straight : straight_statements exception_pc_137_mid.
Proof. vm_compute. exact I. Qed.
Lemma exception_pc_137_mid_safe : formal_typed_suffix_safe flat_memories 137 exception_pc_137_mid.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma exception_pc_137_tail_safe : formal_typed_suffix_safe flat_memories 137 exception_pc_137_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma exception_pc_137_nonregister : has_register 137 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem exception_pc_137_value invalid old current result source value :
 VM.find 776 old = Some source ->
 adapt_hvalue_as_type source (Gtyp (Fuint 32)) = Some value ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 137 result = Some value.
Proof.
 intros Source Adapt Step.
 exact (declared_connection_value 114 flat_statements exception_pc_137_decl exception_pc_137_mid exception_pc_137_tail
 137 776 32 source value invalid flat_memories old current result
 exception_pc_137_position exception_pc_137_split exception_pc_137_straight exception_pc_137_mid_safe exception_pc_137_tail_safe exception_pc_137_nonregister
 (Logic.eq_refl _) Source Adapt Step).
Qed.
Definition exception_pc_1472_decl := match straight_drop 1552 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition exception_pc_1472_tail := match straight_drop 8961 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition exception_pc_1472_mid := take_statements 7408 exception_pc_1472_decl.
Lemma exception_pc_1472_position : straight_drop 1551 flat_statements = Some (@Qcons VarOrder.T (@Swire VarOrder.T 1472 (Gtyp (Fuint 32))) exception_pc_1472_decl).
Proof. vm_compute. reflexivity. Qed.
Lemma exception_pc_1472_split : exception_pc_1472_decl = statement_append exception_pc_1472_mid (@Qcons VarOrder.T (@Sfcnct VarOrder.T (@Eid VarOrder.T 1472) (@Eref VarOrder.T (@Eid VarOrder.T 8245))) exception_pc_1472_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma exception_pc_1472_straight : straight_statements exception_pc_1472_mid.
Proof. vm_compute. exact I. Qed.
Lemma exception_pc_1472_mid_safe : formal_typed_suffix_safe flat_memories 1472 exception_pc_1472_mid.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma exception_pc_1472_tail_safe : formal_typed_suffix_safe flat_memories 1472 exception_pc_1472_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma exception_pc_1472_nonregister : has_register 1472 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem exception_pc_1472_value invalid old current result source value :
 VM.find 8245 old = Some source ->
 adapt_hvalue_as_type source (Gtyp (Fuint 32)) = Some value ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 1472 result = Some value.
Proof.
 intros Source Adapt Step.
 exact (declared_connection_value 1551 flat_statements exception_pc_1472_decl exception_pc_1472_mid exception_pc_1472_tail
 1472 8245 32 source value invalid flat_memories old current result
 exception_pc_1472_position exception_pc_1472_split exception_pc_1472_straight exception_pc_1472_mid_safe exception_pc_1472_tail_safe exception_pc_1472_nonregister
 (Logic.eq_refl _) Source Adapt Step).
Qed.
Definition exception_pc_1670_decl := match straight_drop 1750 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition exception_pc_1670_tail := match straight_drop 7888 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition exception_pc_1670_mid := take_statements 6137 exception_pc_1670_decl.
Lemma exception_pc_1670_position : straight_drop 1749 flat_statements = Some (@Qcons VarOrder.T (@Swire VarOrder.T 1670 (Gtyp (Fuint 32))) exception_pc_1670_decl).
Proof. vm_compute. reflexivity. Qed.
Lemma exception_pc_1670_split : exception_pc_1670_decl = statement_append exception_pc_1670_mid (@Qcons VarOrder.T (@Sfcnct VarOrder.T (@Eid VarOrder.T 1670) (@Eref VarOrder.T (@Eid VarOrder.T 1860))) exception_pc_1670_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma exception_pc_1670_straight : straight_statements exception_pc_1670_mid.
Proof. vm_compute. exact I. Qed.
Lemma exception_pc_1670_mid_safe : formal_typed_suffix_safe flat_memories 1670 exception_pc_1670_mid.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma exception_pc_1670_tail_safe : formal_typed_suffix_safe flat_memories 1670 exception_pc_1670_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma exception_pc_1670_nonregister : has_register 1670 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem exception_pc_1670_value invalid old current result source value :
 VM.find 1860 old = Some source ->
 adapt_hvalue_as_type source (Gtyp (Fuint 32)) = Some value ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 1670 result = Some value.
Proof.
 intros Source Adapt Step.
 exact (declared_connection_value 1749 flat_statements exception_pc_1670_decl exception_pc_1670_mid exception_pc_1670_tail
 1670 1860 32 source value invalid flat_memories old current result
 exception_pc_1670_position exception_pc_1670_split exception_pc_1670_straight exception_pc_1670_mid_safe exception_pc_1670_tail_safe exception_pc_1670_nonregister
 (Logic.eq_refl _) Source Adapt Step).
Qed.
Definition exception_pc_1860_decl := match straight_drop 1940 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition exception_pc_1860_tail := match straight_drop 7431 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition exception_pc_1860_mid := take_statements 5490 exception_pc_1860_decl.
Lemma exception_pc_1860_position : straight_drop 1939 flat_statements = Some (@Qcons VarOrder.T (@Swire VarOrder.T 1860 (Gtyp (Fuint 32))) exception_pc_1860_decl).
Proof. vm_compute. reflexivity. Qed.
Lemma exception_pc_1860_split : exception_pc_1860_decl = statement_append exception_pc_1860_mid (@Qcons VarOrder.T (@Sfcnct VarOrder.T (@Eid VarOrder.T 1860) (@Eref VarOrder.T (@Eid VarOrder.T 7206))) exception_pc_1860_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma exception_pc_1860_straight : straight_statements exception_pc_1860_mid.
Proof. vm_compute. exact I. Qed.
Lemma exception_pc_1860_mid_safe : formal_typed_suffix_safe flat_memories 1860 exception_pc_1860_mid.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma exception_pc_1860_tail_safe : formal_typed_suffix_safe flat_memories 1860 exception_pc_1860_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma exception_pc_1860_nonregister : has_register 1860 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem exception_pc_1860_value invalid old current result source value :
 VM.find 7206 old = Some source ->
 adapt_hvalue_as_type source (Gtyp (Fuint 32)) = Some value ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 1860 result = Some value.
Proof.
 intros Source Adapt Step.
 exact (declared_connection_value 1939 flat_statements exception_pc_1860_decl exception_pc_1860_mid exception_pc_1860_tail
 1860 7206 32 source value invalid flat_memories old current result
 exception_pc_1860_position exception_pc_1860_split exception_pc_1860_straight exception_pc_1860_mid_safe exception_pc_1860_tail_safe exception_pc_1860_nonregister
 (Logic.eq_refl _) Source Adapt Step).
Qed.
Print Assumptions exception_pc_1860_value.
