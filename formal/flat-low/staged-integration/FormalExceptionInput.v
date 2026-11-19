Require Import FormalDeclaredConnection ScalarNodeFrames FormalStatementSegments FormalTypedNodeFrames FormalTypedNodeEquation CoreSocModel ComparisonNodes RegisterInvariants.
From Coq Require Import ZArith.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory FormalInitialization.
Local Open Scope N_scope.
Definition exception_input_decl_128 := match straight_drop 106 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition exception_input_tail_128 := match straight_drop 757 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition exception_input_mid_128 := take_statements 650 exception_input_decl_128.
Lemma exception_input_position_128 : straight_drop 105 flat_statements = Some (@Qcons VarOrder.T (@Swire VarOrder.T 128 (Gtyp (Fuint 1))) exception_input_decl_128).
Proof. vm_compute. reflexivity. Qed.
Lemma exception_input_split_128 : exception_input_decl_128 = statement_append exception_input_mid_128 (@Qcons VarOrder.T (@Sfcnct VarOrder.T (@Eid VarOrder.T 128) (@Eref VarOrder.T (@Eid VarOrder.T 442))) exception_input_tail_128).
Proof. vm_compute. reflexivity. Qed.
Lemma exception_input_straight_128 : straight_statements exception_input_mid_128.
Proof. vm_compute. exact I. Qed.
Lemma exception_input_mid_safe_128 : formal_typed_suffix_safe flat_memories 128 exception_input_mid_128.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma exception_input_tail_safe_128 : formal_typed_suffix_safe flat_memories 128 exception_input_tail_128.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma exception_input_nonregister_128 : has_register 128 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem exception_input_connection_128 invalid old current result source_value value :
 VM.find 442 old = Some source_value ->
 adapt_hvalue_as_type source_value (Gtyp (Fuint 1)) = Some value ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 128 result = Some value.
Proof.
 intros Source Adapt Step.
 exact (declared_connection_value 105 flat_statements exception_input_decl_128 exception_input_mid_128 exception_input_tail_128
 128 442 1 source_value value invalid flat_memories old current result
 exception_input_position_128 exception_input_split_128 exception_input_straight_128 exception_input_mid_safe_128 exception_input_tail_safe_128
 exception_input_nonregister_128 (Logic.eq_refl _) Source Adapt Step).
Qed.
Lemma exception_input_boolean invalid old current result b :
 VM.find 442 old = Some (Gval (Fuint 1) [::b]) ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 128 result = Some (Gval (Fuint 1) [::b]).
Proof. intros Source Step. eapply exception_input_connection_128;
 [exact Source|destruct b; reflexivity|exact Step]. Qed.
Print Assumptions exception_input_boolean.
