Require Import InterruptZeroNodes.
Require Import CoreSocModel ComparisonNodes RegisterInvariants ScalarNodeFrames FormalTypedNodeFrames FormalTypedNodeEquation FormalDeclaredConnection FormalStatementSegments.
From Coq Require Import ZArith.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Definition interrupt_135_decl := match straight_drop 113 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition interrupt_135_tail := match straight_drop 762 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition interrupt_135_mid := take_statements 648 interrupt_135_decl.
Lemma interrupt_135_position : straight_drop 112 flat_statements = Some (@Qcons VarOrder.T (@Swire VarOrder.T 135 (Gtyp (Fuint 32))) interrupt_135_decl).
Proof. vm_compute. reflexivity. Qed.
Lemma interrupt_135_split : interrupt_135_decl = statement_append interrupt_135_mid (@Qcons VarOrder.T (@Sfcnct VarOrder.T (@Eid VarOrder.T 135) (@Eref VarOrder.T (@Eid VarOrder.T 774))) interrupt_135_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma interrupt_135_straight : straight_statements interrupt_135_mid.
Proof. vm_compute. exact I. Qed.
Lemma interrupt_135_mid_safe : formal_typed_suffix_safe flat_memories 135 interrupt_135_mid.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma interrupt_135_tail_safe : formal_typed_suffix_safe flat_memories 135 interrupt_135_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma interrupt_135_nonregister : has_register 135 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem interrupt_135_zero invalid old current result :
 VM.find 774 old = Some (Gval (Fuint 32) interrupt_zero) ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 135 result = Some (Gval (Fuint 32) interrupt_zero).
Proof.
 intros Source Step.
 exact (declared_connection_value 112 flat_statements interrupt_135_decl interrupt_135_mid interrupt_135_tail 135 774 32
 (Gval (Fuint 32) interrupt_zero) (Gval (Fuint 32) interrupt_zero) invalid flat_memories old current result
 interrupt_135_position interrupt_135_split interrupt_135_straight interrupt_135_mid_safe interrupt_135_tail_safe interrupt_135_nonregister
 (Logic.eq_refl _) Source (Logic.eq_refl _) Step).
Qed.
Definition interrupt_1470_decl := match straight_drop 1550 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition interrupt_1470_tail := match straight_drop 8959 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition interrupt_1470_mid := take_statements 7408 interrupt_1470_decl.
Lemma interrupt_1470_position : straight_drop 1549 flat_statements = Some (@Qcons VarOrder.T (@Swire VarOrder.T 1470 (Gtyp (Fuint 32))) interrupt_1470_decl).
Proof. vm_compute. reflexivity. Qed.
Lemma interrupt_1470_split : interrupt_1470_decl = statement_append interrupt_1470_mid (@Qcons VarOrder.T (@Sfcnct VarOrder.T (@Eid VarOrder.T 1470) (@Eref VarOrder.T (@Eid VarOrder.T 8243))) interrupt_1470_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma interrupt_1470_straight : straight_statements interrupt_1470_mid.
Proof. vm_compute. exact I. Qed.
Lemma interrupt_1470_mid_safe : formal_typed_suffix_safe flat_memories 1470 interrupt_1470_mid.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma interrupt_1470_tail_safe : formal_typed_suffix_safe flat_memories 1470 interrupt_1470_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma interrupt_1470_nonregister : has_register 1470 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem interrupt_1470_zero invalid old current result :
 VM.find 8243 old = Some (Gval (Fuint 32) interrupt_zero) ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 1470 result = Some (Gval (Fuint 32) interrupt_zero).
Proof.
 intros Source Step.
 exact (declared_connection_value 1549 flat_statements interrupt_1470_decl interrupt_1470_mid interrupt_1470_tail 1470 8243 32
 (Gval (Fuint 32) interrupt_zero) (Gval (Fuint 32) interrupt_zero) invalid flat_memories old current result
 interrupt_1470_position interrupt_1470_split interrupt_1470_straight interrupt_1470_mid_safe interrupt_1470_tail_safe interrupt_1470_nonregister
 (Logic.eq_refl _) Source (Logic.eq_refl _) Step).
Qed.
Definition interrupt_1668_decl := match straight_drop 1748 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition interrupt_1668_tail := match straight_drop 7886 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition interrupt_1668_mid := take_statements 6137 interrupt_1668_decl.
Lemma interrupt_1668_position : straight_drop 1747 flat_statements = Some (@Qcons VarOrder.T (@Swire VarOrder.T 1668 (Gtyp (Fuint 32))) interrupt_1668_decl).
Proof. vm_compute. reflexivity. Qed.
Lemma interrupt_1668_split : interrupt_1668_decl = statement_append interrupt_1668_mid (@Qcons VarOrder.T (@Sfcnct VarOrder.T (@Eid VarOrder.T 1668) (@Eref VarOrder.T (@Eid VarOrder.T 1858))) interrupt_1668_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma interrupt_1668_straight : straight_statements interrupt_1668_mid.
Proof. vm_compute. exact I. Qed.
Lemma interrupt_1668_mid_safe : formal_typed_suffix_safe flat_memories 1668 interrupt_1668_mid.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma interrupt_1668_tail_safe : formal_typed_suffix_safe flat_memories 1668 interrupt_1668_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma interrupt_1668_nonregister : has_register 1668 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem interrupt_1668_zero invalid old current result :
 VM.find 1858 old = Some (Gval (Fuint 32) interrupt_zero) ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 1668 result = Some (Gval (Fuint 32) interrupt_zero).
Proof.
 intros Source Step.
 exact (declared_connection_value 1747 flat_statements interrupt_1668_decl interrupt_1668_mid interrupt_1668_tail 1668 1858 32
 (Gval (Fuint 32) interrupt_zero) (Gval (Fuint 32) interrupt_zero) invalid flat_memories old current result
 interrupt_1668_position interrupt_1668_split interrupt_1668_straight interrupt_1668_mid_safe interrupt_1668_tail_safe interrupt_1668_nonregister
 (Logic.eq_refl _) Source (Logic.eq_refl _) Step).
Qed.
Definition interrupt_1858_decl := match straight_drop 1938 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition interrupt_1858_tail := match straight_drop 7429 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition interrupt_1858_mid := take_statements 5490 interrupt_1858_decl.
Lemma interrupt_1858_position : straight_drop 1937 flat_statements = Some (@Qcons VarOrder.T (@Swire VarOrder.T 1858 (Gtyp (Fuint 32))) interrupt_1858_decl).
Proof. vm_compute. reflexivity. Qed.
Lemma interrupt_1858_split : interrupt_1858_decl = statement_append interrupt_1858_mid (@Qcons VarOrder.T (@Sfcnct VarOrder.T (@Eid VarOrder.T 1858) (@Eref VarOrder.T (@Eid VarOrder.T 7204))) interrupt_1858_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma interrupt_1858_straight : straight_statements interrupt_1858_mid.
Proof. vm_compute. exact I. Qed.
Lemma interrupt_1858_mid_safe : formal_typed_suffix_safe flat_memories 1858 interrupt_1858_mid.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma interrupt_1858_tail_safe : formal_typed_suffix_safe flat_memories 1858 interrupt_1858_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma interrupt_1858_nonregister : has_register 1858 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem interrupt_1858_zero invalid old current result :
 VM.find 7204 old = Some (Gval (Fuint 32) interrupt_zero) ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 1858 result = Some (Gval (Fuint 32) interrupt_zero).
Proof.
 intros Source Step.
 exact (declared_connection_value 1937 flat_statements interrupt_1858_decl interrupt_1858_mid interrupt_1858_tail 1858 7204 32
 (Gval (Fuint 32) interrupt_zero) (Gval (Fuint 32) interrupt_zero) invalid flat_memories old current result
 interrupt_1858_position interrupt_1858_split interrupt_1858_straight interrupt_1858_mid_safe interrupt_1858_tail_safe interrupt_1858_nonregister
 (Logic.eq_refl _) Source (Logic.eq_refl _) Step).
Qed.
Print Assumptions interrupt_1858_zero.
