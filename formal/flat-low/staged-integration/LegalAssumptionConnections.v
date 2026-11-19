Require Import CoreSocModel ComparisonNodes FormalDeclaredConnection FormalDeclaredConnectionObservation FormalStatementSegments FormalTypedNodeFrames FormalTypedNodeEquation ScalarNodeFrames RegisterInvariants.
From Coq Require Import ZArith.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Definition legal_connection_63_decl := match straight_drop 41 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition legal_connection_63_tail := match straight_drop 9982 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition legal_connection_63_mid := take_statements 9940 legal_connection_63_decl.
Lemma legal_connection_63_position : straight_drop 40 flat_statements = Some (@Qcons VarOrder.T (@Swire VarOrder.T 63 (Gtyp (Fuint 1))) legal_connection_63_decl).
Proof. vm_compute. reflexivity. Qed.
Lemma legal_connection_63_split : legal_connection_63_decl = statement_append legal_connection_63_mid (@Qcons VarOrder.T (@Sfcnct VarOrder.T (@Eid VarOrder.T 63) (@Eref VarOrder.T (@Eid VarOrder.T 9141))) legal_connection_63_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma legal_connection_63_straight : straight_statements legal_connection_63_mid.
Proof. vm_compute. exact I. Qed.
Lemma legal_connection_63_mid_safe : formal_typed_suffix_safe flat_memories 63 legal_connection_63_mid.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma legal_connection_63_tail_safe : formal_typed_suffix_safe flat_memories 63 legal_connection_63_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma legal_connection_63_nonregister : has_register 63 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem legal_connection_63_observation invalid old current result :
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 exists source_value value, VM.find 9141 old = Some source_value /\
 adapt_hvalue_as_type source_value (Gtyp (Fuint 1)) = Some value /\ VM.find 63 result = Some value.
Proof.
 intro Step. exact (declared_connection_observation 40 flat_statements legal_connection_63_decl legal_connection_63_mid legal_connection_63_tail
 63 9141 1 invalid flat_memories old current result
 legal_connection_63_position legal_connection_63_split legal_connection_63_straight legal_connection_63_mid_safe legal_connection_63_tail_safe legal_connection_63_nonregister
 (Logic.eq_refl _) Step).
Qed.
Theorem legal_connection_63_value invalid old current result source_value value :
 VM.find 9141 old = Some source_value ->
 adapt_hvalue_as_type source_value (Gtyp (Fuint 1)) = Some value ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 63 result = Some value.
Proof.
 intros Source Adapt Step. exact (declared_connection_value 40 flat_statements legal_connection_63_decl legal_connection_63_mid legal_connection_63_tail
 63 9141 1 source_value value invalid flat_memories old current result
 legal_connection_63_position legal_connection_63_split legal_connection_63_straight legal_connection_63_mid_safe legal_connection_63_tail_safe legal_connection_63_nonregister
 (Logic.eq_refl _) Source Adapt Step).
Qed.
Definition legal_connection_45_decl := match straight_drop 23 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition legal_connection_45_tail := match straight_drop 9964 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition legal_connection_45_mid := take_statements 9940 legal_connection_45_decl.
Lemma legal_connection_45_position : straight_drop 22 flat_statements = Some (@Qcons VarOrder.T (@Swire VarOrder.T 45 (Gtyp (Fuint 1))) legal_connection_45_decl).
Proof. vm_compute. reflexivity. Qed.
Lemma legal_connection_45_split : legal_connection_45_decl = statement_append legal_connection_45_mid (@Qcons VarOrder.T (@Sfcnct VarOrder.T (@Eid VarOrder.T 45) (@Eref VarOrder.T (@Eid VarOrder.T 9157))) legal_connection_45_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma legal_connection_45_straight : straight_statements legal_connection_45_mid.
Proof. vm_compute. exact I. Qed.
Lemma legal_connection_45_mid_safe : formal_typed_suffix_safe flat_memories 45 legal_connection_45_mid.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma legal_connection_45_tail_safe : formal_typed_suffix_safe flat_memories 45 legal_connection_45_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma legal_connection_45_nonregister : has_register 45 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem legal_connection_45_observation invalid old current result :
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 exists source_value value, VM.find 9157 old = Some source_value /\
 adapt_hvalue_as_type source_value (Gtyp (Fuint 1)) = Some value /\ VM.find 45 result = Some value.
Proof.
 intro Step. exact (declared_connection_observation 22 flat_statements legal_connection_45_decl legal_connection_45_mid legal_connection_45_tail
 45 9157 1 invalid flat_memories old current result
 legal_connection_45_position legal_connection_45_split legal_connection_45_straight legal_connection_45_mid_safe legal_connection_45_tail_safe legal_connection_45_nonregister
 (Logic.eq_refl _) Step).
Qed.
Theorem legal_connection_45_value invalid old current result source_value value :
 VM.find 9157 old = Some source_value ->
 adapt_hvalue_as_type source_value (Gtyp (Fuint 1)) = Some value ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 45 result = Some value.
Proof.
 intros Source Adapt Step. exact (declared_connection_value 22 flat_statements legal_connection_45_decl legal_connection_45_mid legal_connection_45_tail
 45 9157 1 source_value value invalid flat_memories old current result
 legal_connection_45_position legal_connection_45_split legal_connection_45_straight legal_connection_45_mid_safe legal_connection_45_tail_safe legal_connection_45_nonregister
 (Logic.eq_refl _) Source Adapt Step).
Qed.
Definition legal_connection_100_decl := match straight_drop 78 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition legal_connection_100_tail := match straight_drop 8769 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition legal_connection_100_mid := take_statements 8690 legal_connection_100_decl.
Lemma legal_connection_100_position : straight_drop 77 flat_statements = Some (@Qcons VarOrder.T (@Swire VarOrder.T 100 (Gtyp (Fuint 1))) legal_connection_100_decl).
Proof. vm_compute. reflexivity. Qed.
Lemma legal_connection_100_split : legal_connection_100_decl = statement_append legal_connection_100_mid (@Qcons VarOrder.T (@Sfcnct VarOrder.T (@Eid VarOrder.T 100) (@Eref VarOrder.T (@Eid VarOrder.T 139))) legal_connection_100_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma legal_connection_100_straight : straight_statements legal_connection_100_mid.
Proof. vm_compute. exact I. Qed.
Lemma legal_connection_100_mid_safe : formal_typed_suffix_safe flat_memories 100 legal_connection_100_mid.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma legal_connection_100_tail_safe : formal_typed_suffix_safe flat_memories 100 legal_connection_100_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma legal_connection_100_nonregister : has_register 100 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem legal_connection_100_observation invalid old current result :
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 exists source_value value, VM.find 139 old = Some source_value /\
 adapt_hvalue_as_type source_value (Gtyp (Fuint 1)) = Some value /\ VM.find 100 result = Some value.
Proof.
 intro Step. exact (declared_connection_observation 77 flat_statements legal_connection_100_decl legal_connection_100_mid legal_connection_100_tail
 100 139 1 invalid flat_memories old current result
 legal_connection_100_position legal_connection_100_split legal_connection_100_straight legal_connection_100_mid_safe legal_connection_100_tail_safe legal_connection_100_nonregister
 (Logic.eq_refl _) Step).
Qed.
Theorem legal_connection_100_value invalid old current result source_value value :
 VM.find 139 old = Some source_value ->
 adapt_hvalue_as_type source_value (Gtyp (Fuint 1)) = Some value ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 100 result = Some value.
Proof.
 intros Source Adapt Step. exact (declared_connection_value 77 flat_statements legal_connection_100_decl legal_connection_100_mid legal_connection_100_tail
 100 139 1 source_value value invalid flat_memories old current result
 legal_connection_100_position legal_connection_100_split legal_connection_100_straight legal_connection_100_mid_safe legal_connection_100_tail_safe legal_connection_100_nonregister
 (Logic.eq_refl _) Source Adapt Step).
Qed.
Print Assumptions legal_connection_63_observation.
