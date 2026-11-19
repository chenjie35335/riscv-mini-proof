Require Import CoreSocModel ComparisonNodes RegisterInvariants ScalarNodeFrames FormalTypedNodeFrames FormalTypedNodeEquation FormalDeclaredConnection FormalStatementSegments.
From Coq Require Import ZArith.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Definition exception_event_134_decl := match straight_drop 112 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition exception_event_134_tail := match straight_drop 761 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition exception_event_134_mid := take_statements 648 exception_event_134_decl.
Lemma exception_event_134_position : straight_drop 111 flat_statements = Some (@Qcons VarOrder.T (@Swire VarOrder.T 134 (Gtyp (Fuint 1))) exception_event_134_decl).
Proof. vm_compute. reflexivity. Qed.
Lemma exception_event_134_split : exception_event_134_decl = statement_append exception_event_134_mid (@Qcons VarOrder.T (@Sfcnct VarOrder.T (@Eid VarOrder.T 134) (@Eref VarOrder.T (@Eid VarOrder.T 773))) exception_event_134_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma exception_event_134_straight : straight_statements exception_event_134_mid.
Proof. vm_compute. exact I. Qed.
Lemma exception_event_134_mid_safe : formal_typed_suffix_safe flat_memories 134 exception_event_134_mid.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma exception_event_134_tail_safe : formal_typed_suffix_safe flat_memories 134 exception_event_134_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma exception_event_134_nonregister : has_register 134 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem exception_event_134_value invalid old current result source value :
 VM.find 773 old = Some source ->
 adapt_hvalue_as_type source (Gtyp (Fuint 1)) = Some value ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 134 result = Some value.
Proof.
 intros Source Adapt Step.
 exact (declared_connection_value 111 flat_statements exception_event_134_decl exception_event_134_mid exception_event_134_tail
 134 773 1 source value invalid flat_memories old current result
 exception_event_134_position exception_event_134_split exception_event_134_straight exception_event_134_mid_safe exception_event_134_tail_safe exception_event_134_nonregister
 (Logic.eq_refl _) Source Adapt Step).
Qed.
Definition exception_event_139_decl := match straight_drop 117 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition exception_event_139_tail := match straight_drop 766 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition exception_event_139_mid := take_statements 648 exception_event_139_decl.
Lemma exception_event_139_position : straight_drop 116 flat_statements = Some (@Qcons VarOrder.T (@Swire VarOrder.T 139 (Gtyp (Fuint 1))) exception_event_139_decl).
Proof. vm_compute. reflexivity. Qed.
Lemma exception_event_139_split : exception_event_139_decl = statement_append exception_event_139_mid (@Qcons VarOrder.T (@Sfcnct VarOrder.T (@Eid VarOrder.T 139) (@Eref VarOrder.T (@Eid VarOrder.T 128))) exception_event_139_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma exception_event_139_straight : straight_statements exception_event_139_mid.
Proof. vm_compute. exact I. Qed.
Lemma exception_event_139_mid_safe : formal_typed_suffix_safe flat_memories 139 exception_event_139_mid.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma exception_event_139_tail_safe : formal_typed_suffix_safe flat_memories 139 exception_event_139_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma exception_event_139_nonregister : has_register 139 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem exception_event_139_value invalid old current result source value :
 VM.find 128 old = Some source ->
 adapt_hvalue_as_type source (Gtyp (Fuint 1)) = Some value ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 139 result = Some value.
Proof.
 intros Source Adapt Step.
 exact (declared_connection_value 116 flat_statements exception_event_139_decl exception_event_139_mid exception_event_139_tail
 139 128 1 source value invalid flat_memories old current result
 exception_event_139_position exception_event_139_split exception_event_139_straight exception_event_139_mid_safe exception_event_139_tail_safe exception_event_139_nonregister
 (Logic.eq_refl _) Source Adapt Step).
Qed.
Definition exception_event_1469_decl := match straight_drop 1549 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition exception_event_1469_tail := match straight_drop 8958 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition exception_event_1469_mid := take_statements 7408 exception_event_1469_decl.
Lemma exception_event_1469_position : straight_drop 1548 flat_statements = Some (@Qcons VarOrder.T (@Swire VarOrder.T 1469 (Gtyp (Fuint 1))) exception_event_1469_decl).
Proof. vm_compute. reflexivity. Qed.
Lemma exception_event_1469_split : exception_event_1469_decl = statement_append exception_event_1469_mid (@Qcons VarOrder.T (@Sfcnct VarOrder.T (@Eid VarOrder.T 1469) (@Eref VarOrder.T (@Eid VarOrder.T 8242))) exception_event_1469_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma exception_event_1469_straight : straight_statements exception_event_1469_mid.
Proof. vm_compute. exact I. Qed.
Lemma exception_event_1469_mid_safe : formal_typed_suffix_safe flat_memories 1469 exception_event_1469_mid.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma exception_event_1469_tail_safe : formal_typed_suffix_safe flat_memories 1469 exception_event_1469_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma exception_event_1469_nonregister : has_register 1469 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem exception_event_1469_value invalid old current result source value :
 VM.find 8242 old = Some source ->
 adapt_hvalue_as_type source (Gtyp (Fuint 1)) = Some value ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 1469 result = Some value.
Proof.
 intros Source Adapt Step.
 exact (declared_connection_value 1548 flat_statements exception_event_1469_decl exception_event_1469_mid exception_event_1469_tail
 1469 8242 1 source value invalid flat_memories old current result
 exception_event_1469_position exception_event_1469_split exception_event_1469_straight exception_event_1469_mid_safe exception_event_1469_tail_safe exception_event_1469_nonregister
 (Logic.eq_refl _) Source Adapt Step).
Qed.
Print Assumptions exception_event_1469_value.
