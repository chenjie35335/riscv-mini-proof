Require Import CoreSocModel ComparisonNodes RegisterInvariants ScalarNodeFrames FormalTypedNodeFrames FormalTypedNodeEquation FormalDeclaredConnection FormalStatementSegments.
From Coq Require Import ZArith.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Definition exception_instruction_123_decl := match straight_drop 101 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition exception_instruction_123_tail := match straight_drop 8791 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition exception_instruction_123_mid := take_statements 8689 exception_instruction_123_decl.
Lemma exception_instruction_123_position : straight_drop 100 flat_statements = Some (@Qcons VarOrder.T (@Swire VarOrder.T 123 (Gtyp (Fuint 32))) exception_instruction_123_decl).
Proof. vm_compute. reflexivity. Qed.
Lemma exception_instruction_123_split : exception_instruction_123_decl = statement_append exception_instruction_123_mid (@Qcons VarOrder.T (@Sfcnct VarOrder.T (@Eid VarOrder.T 123) (@Eref VarOrder.T (@Eid VarOrder.T 7750))) exception_instruction_123_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma exception_instruction_123_straight : straight_statements exception_instruction_123_mid.
Proof. vm_compute. exact I. Qed.
Lemma exception_instruction_123_mid_safe : formal_typed_suffix_safe flat_memories 123 exception_instruction_123_mid.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma exception_instruction_123_tail_safe : formal_typed_suffix_safe flat_memories 123 exception_instruction_123_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma exception_instruction_123_nonregister : has_register 123 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem exception_instruction_123_value invalid old current result source value :
 VM.find 7750 old = Some source ->
 adapt_hvalue_as_type source (Gtyp (Fuint 32)) = Some value ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 123 result = Some value.
Proof.
 intros Source Adapt Step.
 exact (declared_connection_value 100 flat_statements exception_instruction_123_decl exception_instruction_123_mid exception_instruction_123_tail
 123 7750 32 source value invalid flat_memories old current result
 exception_instruction_123_position exception_instruction_123_split exception_instruction_123_straight exception_instruction_123_mid_safe exception_instruction_123_tail_safe exception_instruction_123_nonregister
 (Logic.eq_refl _) Source Adapt Step).
Qed.
Definition exception_instruction_138_decl := match straight_drop 116 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition exception_instruction_138_tail := match straight_drop 765 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition exception_instruction_138_mid := take_statements 648 exception_instruction_138_decl.
Lemma exception_instruction_138_position : straight_drop 115 flat_statements = Some (@Qcons VarOrder.T (@Swire VarOrder.T 138 (Gtyp (Fuint 32))) exception_instruction_138_decl).
Proof. vm_compute. reflexivity. Qed.
Lemma exception_instruction_138_split : exception_instruction_138_decl = statement_append exception_instruction_138_mid (@Qcons VarOrder.T (@Sfcnct VarOrder.T (@Eid VarOrder.T 138) (@Eref VarOrder.T (@Eid VarOrder.T 777))) exception_instruction_138_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma exception_instruction_138_straight : straight_statements exception_instruction_138_mid.
Proof. vm_compute. exact I. Qed.
Lemma exception_instruction_138_mid_safe : formal_typed_suffix_safe flat_memories 138 exception_instruction_138_mid.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma exception_instruction_138_tail_safe : formal_typed_suffix_safe flat_memories 138 exception_instruction_138_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma exception_instruction_138_nonregister : has_register 138 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem exception_instruction_138_value invalid old current result source value :
 VM.find 777 old = Some source ->
 adapt_hvalue_as_type source (Gtyp (Fuint 32)) = Some value ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 138 result = Some value.
Proof.
 intros Source Adapt Step.
 exact (declared_connection_value 115 flat_statements exception_instruction_138_decl exception_instruction_138_mid exception_instruction_138_tail
 138 777 32 source value invalid flat_memories old current result
 exception_instruction_138_position exception_instruction_138_split exception_instruction_138_straight exception_instruction_138_mid_safe exception_instruction_138_tail_safe exception_instruction_138_nonregister
 (Logic.eq_refl _) Source Adapt Step).
Qed.
Definition exception_instruction_1473_decl := match straight_drop 1553 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition exception_instruction_1473_tail := match straight_drop 8962 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition exception_instruction_1473_mid := take_statements 7408 exception_instruction_1473_decl.
Lemma exception_instruction_1473_position : straight_drop 1552 flat_statements = Some (@Qcons VarOrder.T (@Swire VarOrder.T 1473 (Gtyp (Fuint 32))) exception_instruction_1473_decl).
Proof. vm_compute. reflexivity. Qed.
Lemma exception_instruction_1473_split : exception_instruction_1473_decl = statement_append exception_instruction_1473_mid (@Qcons VarOrder.T (@Sfcnct VarOrder.T (@Eid VarOrder.T 1473) (@Eref VarOrder.T (@Eid VarOrder.T 8246))) exception_instruction_1473_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma exception_instruction_1473_straight : straight_statements exception_instruction_1473_mid.
Proof. vm_compute. exact I. Qed.
Lemma exception_instruction_1473_mid_safe : formal_typed_suffix_safe flat_memories 1473 exception_instruction_1473_mid.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma exception_instruction_1473_tail_safe : formal_typed_suffix_safe flat_memories 1473 exception_instruction_1473_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma exception_instruction_1473_nonregister : has_register 1473 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem exception_instruction_1473_value invalid old current result source value :
 VM.find 8246 old = Some source ->
 adapt_hvalue_as_type source (Gtyp (Fuint 32)) = Some value ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 1473 result = Some value.
Proof.
 intros Source Adapt Step.
 exact (declared_connection_value 1552 flat_statements exception_instruction_1473_decl exception_instruction_1473_mid exception_instruction_1473_tail
 1473 8246 32 source value invalid flat_memories old current result
 exception_instruction_1473_position exception_instruction_1473_split exception_instruction_1473_straight exception_instruction_1473_mid_safe exception_instruction_1473_tail_safe exception_instruction_1473_nonregister
 (Logic.eq_refl _) Source Adapt Step).
Qed.
Definition exception_instruction_1671_decl := match straight_drop 1751 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition exception_instruction_1671_tail := match straight_drop 7889 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition exception_instruction_1671_mid := take_statements 6137 exception_instruction_1671_decl.
Lemma exception_instruction_1671_position : straight_drop 1750 flat_statements = Some (@Qcons VarOrder.T (@Swire VarOrder.T 1671 (Gtyp (Fuint 32))) exception_instruction_1671_decl).
Proof. vm_compute. reflexivity. Qed.
Lemma exception_instruction_1671_split : exception_instruction_1671_decl = statement_append exception_instruction_1671_mid (@Qcons VarOrder.T (@Sfcnct VarOrder.T (@Eid VarOrder.T 1671) (@Eref VarOrder.T (@Eid VarOrder.T 1861))) exception_instruction_1671_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma exception_instruction_1671_straight : straight_statements exception_instruction_1671_mid.
Proof. vm_compute. exact I. Qed.
Lemma exception_instruction_1671_mid_safe : formal_typed_suffix_safe flat_memories 1671 exception_instruction_1671_mid.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma exception_instruction_1671_tail_safe : formal_typed_suffix_safe flat_memories 1671 exception_instruction_1671_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma exception_instruction_1671_nonregister : has_register 1671 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem exception_instruction_1671_value invalid old current result source value :
 VM.find 1861 old = Some source ->
 adapt_hvalue_as_type source (Gtyp (Fuint 32)) = Some value ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 1671 result = Some value.
Proof.
 intros Source Adapt Step.
 exact (declared_connection_value 1750 flat_statements exception_instruction_1671_decl exception_instruction_1671_mid exception_instruction_1671_tail
 1671 1861 32 source value invalid flat_memories old current result
 exception_instruction_1671_position exception_instruction_1671_split exception_instruction_1671_straight exception_instruction_1671_mid_safe exception_instruction_1671_tail_safe exception_instruction_1671_nonregister
 (Logic.eq_refl _) Source Adapt Step).
Qed.
Definition exception_instruction_1861_decl := match straight_drop 1941 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition exception_instruction_1861_tail := match straight_drop 7432 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition exception_instruction_1861_mid := take_statements 5490 exception_instruction_1861_decl.
Lemma exception_instruction_1861_position : straight_drop 1940 flat_statements = Some (@Qcons VarOrder.T (@Swire VarOrder.T 1861 (Gtyp (Fuint 32))) exception_instruction_1861_decl).
Proof. vm_compute. reflexivity. Qed.
Lemma exception_instruction_1861_split : exception_instruction_1861_decl = statement_append exception_instruction_1861_mid (@Qcons VarOrder.T (@Sfcnct VarOrder.T (@Eid VarOrder.T 1861) (@Eref VarOrder.T (@Eid VarOrder.T 7207))) exception_instruction_1861_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma exception_instruction_1861_straight : straight_statements exception_instruction_1861_mid.
Proof. vm_compute. exact I. Qed.
Lemma exception_instruction_1861_mid_safe : formal_typed_suffix_safe flat_memories 1861 exception_instruction_1861_mid.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma exception_instruction_1861_tail_safe : formal_typed_suffix_safe flat_memories 1861 exception_instruction_1861_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma exception_instruction_1861_nonregister : has_register 1861 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem exception_instruction_1861_value invalid old current result source value :
 VM.find 7207 old = Some source ->
 adapt_hvalue_as_type source (Gtyp (Fuint 32)) = Some value ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 1861 result = Some value.
Proof.
 intros Source Adapt Step.
 exact (declared_connection_value 1940 flat_statements exception_instruction_1861_decl exception_instruction_1861_mid exception_instruction_1861_tail
 1861 7207 32 source value invalid flat_memories old current result
 exception_instruction_1861_position exception_instruction_1861_split exception_instruction_1861_straight exception_instruction_1861_mid_safe exception_instruction_1861_tail_safe exception_instruction_1861_nonregister
 (Logic.eq_refl _) Source Adapt Step).
Qed.
Print Assumptions exception_instruction_1861_value.
