Require Import FormalUnaryConnectionObservation FormalDeclaredConnection ScalarNodeFrames FormalStatementSegments FormalTypedNodeFrames FormalTypedNodeEquation CoreSocModel ComparisonNodes RegisterInvariants.
From Coq Require Import ZArith.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From firrtl Require Import Firrtl_with_implicit_widths Env_with_implicit_widths HiEnv_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory FormalInitialization.
Local Open Scope N_scope.
Definition pc_decl_71 := match straight_drop 49 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition pc_tail_71 := match straight_drop 8757 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition pc_mid_71 := take_statements 8707 pc_decl_71.
Lemma pc_position_71 : straight_drop 48 flat_statements = Some (@Qcons VarOrder.T (@Swire VarOrder.T 71 (Gtyp (Fuint 32))) pc_decl_71).
Proof. vm_compute. reflexivity. Qed.
Lemma pc_split_71 : pc_decl_71 = statement_append pc_mid_71 (@Qcons VarOrder.T (@Sfcnct VarOrder.T (@Eid VarOrder.T 71) (@Eprim_unop VarOrder.T (Uextr 31 0) (@Eref VarOrder.T (@Eid VarOrder.T 7781)))) pc_tail_71).
Proof. vm_compute. reflexivity. Qed.
Lemma pc_straight_71 : straight_statements pc_mid_71.
Proof. vm_compute. exact I. Qed.
Lemma pc_mid_safe_71 : formal_typed_suffix_safe flat_memories 71 pc_mid_71.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma pc_tail_safe_71 : formal_typed_suffix_safe flat_memories 71 pc_tail_71.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma pc_nonregister_71 : has_register 71 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem pc_71_observation invalid old current result :
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 exists source value, eval_hfexpr_with_memory flat_memories (@Eprim_unop VarOrder.T (Uextr 31 0) (@Eref VarOrder.T (@Eid VarOrder.T 7781))) old old = Some source /\
 adapt_hvalue_as_type source (Gtyp (Fuint 32)) = Some value /\ VM.find 71 result = Some value.
Proof.
 intro Step. exact (declared_unary_observation 48 flat_statements pc_decl_71 pc_mid_71 pc_tail_71 71 (Uextr 31 0)
 (@Eref VarOrder.T (@Eid VarOrder.T 7781)) invalid flat_memories old current result 32
 pc_position_71 pc_split_71 pc_straight_71 pc_mid_safe_71 pc_tail_safe_71 pc_nonregister_71 Step).
Qed.
Definition pc_decl_30 := match straight_drop 8 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition pc_tail_30 := match straight_drop 9953 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition pc_mid_30 := take_statements 9944 pc_decl_30.
Lemma pc_position_30 : straight_drop 7 flat_statements = Some (@Qcons VarOrder.T (@Swire VarOrder.T 30 (Gtyp (Fuint 32))) pc_decl_30).
Proof. vm_compute. reflexivity. Qed.
Lemma pc_split_30 : pc_decl_30 = statement_append pc_mid_30 (@Qcons VarOrder.T (@Sfcnct VarOrder.T (@Eid VarOrder.T 30) (@Eref VarOrder.T (@Eid VarOrder.T 71))) pc_tail_30).
Proof. vm_compute. reflexivity. Qed.
Lemma pc_straight_30 : straight_statements pc_mid_30.
Proof. vm_compute. exact I. Qed.
Lemma pc_mid_safe_30 : formal_typed_suffix_safe flat_memories 30 pc_mid_30.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma pc_tail_safe_30 : formal_typed_suffix_safe flat_memories 30 pc_tail_30.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma pc_nonregister_30 : has_register 30 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem pc_30_connection invalid old current result source value :
 VM.find 71 old = Some source -> adapt_hvalue_as_type source (Gtyp (Fuint 32)) = Some value ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result -> VM.find 30 result = Some value.
Proof.
 intros Source Adapt Step. exact (declared_connection_value 7 flat_statements pc_decl_30 pc_mid_30 pc_tail_30 30 71 32 source value invalid flat_memories old current result
 pc_position_30 pc_split_30 pc_straight_30 pc_mid_safe_30 pc_tail_safe_30 pc_nonregister_30 (Logic.eq_refl _) Source Adapt Step).
Qed.
Print Assumptions pc_30_connection.
