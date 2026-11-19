Require Import FormalDeclaredConnection ScalarNodeFrames FormalStatementSegments FormalTypedNodeFrames FormalTypedNodeEquation CoreSocModel ComparisonNodes RegisterInvariants.
From Coq Require Import ZArith.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory FormalInitialization.
Local Open Scope N_scope.
Definition x0_register_input_decl_123 := match straight_drop 101 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition x0_register_input_tail_123 := match straight_drop 8791 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition x0_register_input_mid_123 := take_statements 8689 x0_register_input_decl_123.
Lemma x0_register_input_position_123 : straight_drop 100 flat_statements = Some (@Qcons VarOrder.T (@Swire VarOrder.T 123 (Gtyp (Fuint 32))) x0_register_input_decl_123).
Proof. vm_compute. reflexivity. Qed.
Lemma x0_register_input_split_123 : x0_register_input_decl_123 = statement_append x0_register_input_mid_123 (@Qcons VarOrder.T (@Sfcnct VarOrder.T (@Eid VarOrder.T 123) (@Eref VarOrder.T (@Eid VarOrder.T 7750))) x0_register_input_tail_123).
Proof. vm_compute. reflexivity. Qed.
Lemma x0_register_input_straight_123 : straight_statements x0_register_input_mid_123.
Proof. vm_compute. exact I. Qed.
Lemma x0_register_input_mid_safe_123 : formal_typed_suffix_safe flat_memories 123 x0_register_input_mid_123.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma x0_register_input_tail_safe_123 : formal_typed_suffix_safe flat_memories 123 x0_register_input_tail_123.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma x0_register_input_nonregister_123 : has_register 123 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem x0_register_input_connection_123 invalid old current result source_value value :
 VM.find 7750 old = Some source_value ->
 adapt_hvalue_as_type source_value (Gtyp (Fuint 32)) = Some value ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 123 result = Some value.
Proof.
 intros Source Adapt Step.
 exact (declared_connection_value 100 flat_statements x0_register_input_decl_123 x0_register_input_mid_123 x0_register_input_tail_123
 123 7750 32 source_value value invalid flat_memories old current result
 x0_register_input_position_123 x0_register_input_split_123 x0_register_input_straight_123 x0_register_input_mid_safe_123 x0_register_input_tail_safe_123
 x0_register_input_nonregister_123 (Logic.eq_refl _) Source Adapt Step).
Qed.
Theorem x0_register_input_concrete_123 invalid old current result width bits :
 VM.find 7750 old = Some (Gval (Fuint width) bits) ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 exists word, VM.find 123 result = Some (Gval (Fuint 32) word).
Proof.
 intros Source Step. eexists.
 eapply x0_register_input_connection_123; [exact Source|reflexivity|exact Step].
Qed.
Definition x0_register_input_decl_118 := match straight_drop 96 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition x0_register_input_tail_118 := match straight_drop 8787 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition x0_register_input_mid_118 := take_statements 8690 x0_register_input_decl_118.
Lemma x0_register_input_position_118 : straight_drop 95 flat_statements = Some (@Qcons VarOrder.T (@Swire VarOrder.T 118 (Gtyp (Fuint 3))) x0_register_input_decl_118).
Proof. vm_compute. reflexivity. Qed.
Lemma x0_register_input_split_118 : x0_register_input_decl_118 = statement_append x0_register_input_mid_118 (@Qcons VarOrder.T (@Sfcnct VarOrder.T (@Eid VarOrder.T 118) (@Eref VarOrder.T (@Eid VarOrder.T 7758))) x0_register_input_tail_118).
Proof. vm_compute. reflexivity. Qed.
Lemma x0_register_input_straight_118 : straight_statements x0_register_input_mid_118.
Proof. vm_compute. exact I. Qed.
Lemma x0_register_input_mid_safe_118 : formal_typed_suffix_safe flat_memories 118 x0_register_input_mid_118.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma x0_register_input_tail_safe_118 : formal_typed_suffix_safe flat_memories 118 x0_register_input_tail_118.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma x0_register_input_nonregister_118 : has_register 118 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem x0_register_input_connection_118 invalid old current result source_value value :
 VM.find 7758 old = Some source_value ->
 adapt_hvalue_as_type source_value (Gtyp (Fuint 3)) = Some value ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 118 result = Some value.
Proof.
 intros Source Adapt Step.
 exact (declared_connection_value 95 flat_statements x0_register_input_decl_118 x0_register_input_mid_118 x0_register_input_tail_118
 118 7758 3 source_value value invalid flat_memories old current result
 x0_register_input_position_118 x0_register_input_split_118 x0_register_input_straight_118 x0_register_input_mid_safe_118 x0_register_input_tail_safe_118
 x0_register_input_nonregister_118 (Logic.eq_refl _) Source Adapt Step).
Qed.
Theorem x0_register_input_concrete_118 invalid old current result width bits :
 VM.find 7758 old = Some (Gval (Fuint width) bits) ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 exists word, VM.find 118 result = Some (Gval (Fuint 3) word).
Proof.
 intros Source Step. eexists.
 eapply x0_register_input_connection_118; [exact Source|reflexivity|exact Step].
Qed.
Definition x0_register_input_decl_122 := match straight_drop 100 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition x0_register_input_tail_122 := match straight_drop 8790 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition x0_register_input_mid_122 := take_statements 8689 x0_register_input_decl_122.
Lemma x0_register_input_position_122 : straight_drop 99 flat_statements = Some (@Qcons VarOrder.T (@Swire VarOrder.T 122 (Gtyp (Fuint 32))) x0_register_input_decl_122).
Proof. vm_compute. reflexivity. Qed.
Lemma x0_register_input_split_122 : x0_register_input_decl_122 = statement_append x0_register_input_mid_122 (@Qcons VarOrder.T (@Sfcnct VarOrder.T (@Eid VarOrder.T 122) (@Eref VarOrder.T (@Eid VarOrder.T 7752))) x0_register_input_tail_122).
Proof. vm_compute. reflexivity. Qed.
Lemma x0_register_input_straight_122 : straight_statements x0_register_input_mid_122.
Proof. vm_compute. exact I. Qed.
Lemma x0_register_input_mid_safe_122 : formal_typed_suffix_safe flat_memories 122 x0_register_input_mid_122.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma x0_register_input_tail_safe_122 : formal_typed_suffix_safe flat_memories 122 x0_register_input_tail_122.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma x0_register_input_nonregister_122 : has_register 122 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem x0_register_input_connection_122 invalid old current result source_value value :
 VM.find 7752 old = Some source_value ->
 adapt_hvalue_as_type source_value (Gtyp (Fuint 32)) = Some value ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 122 result = Some value.
Proof.
 intros Source Adapt Step.
 exact (declared_connection_value 99 flat_statements x0_register_input_decl_122 x0_register_input_mid_122 x0_register_input_tail_122
 122 7752 32 source_value value invalid flat_memories old current result
 x0_register_input_position_122 x0_register_input_split_122 x0_register_input_straight_122 x0_register_input_mid_safe_122 x0_register_input_tail_safe_122
 x0_register_input_nonregister_122 (Logic.eq_refl _) Source Adapt Step).
Qed.
Theorem x0_register_input_concrete_122 invalid old current result width bits :
 VM.find 7752 old = Some (Gval (Fuint width) bits) ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 exists word, VM.find 122 result = Some (Gval (Fuint 32) word).
Proof.
 intros Source Step. eexists.
 eapply x0_register_input_connection_122; [exact Source|reflexivity|exact Step].
Qed.
Definition x0_register_input_decl_127 := match straight_drop 105 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition x0_register_input_tail_127 := match straight_drop 8795 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition x0_register_input_mid_127 := take_statements 8689 x0_register_input_decl_127.
Lemma x0_register_input_position_127 : straight_drop 104 flat_statements = Some (@Qcons VarOrder.T (@Swire VarOrder.T 127 (Gtyp (Fuint 1))) x0_register_input_decl_127).
Proof. vm_compute. reflexivity. Qed.
Lemma x0_register_input_split_127 : x0_register_input_decl_127 = statement_append x0_register_input_mid_127 (@Qcons VarOrder.T (@Sfcnct VarOrder.T (@Eid VarOrder.T 127) (@Eref VarOrder.T (@Eid VarOrder.T 7760))) x0_register_input_tail_127).
Proof. vm_compute. reflexivity. Qed.
Lemma x0_register_input_straight_127 : straight_statements x0_register_input_mid_127.
Proof. vm_compute. exact I. Qed.
Lemma x0_register_input_mid_safe_127 : formal_typed_suffix_safe flat_memories 127 x0_register_input_mid_127.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma x0_register_input_tail_safe_127 : formal_typed_suffix_safe flat_memories 127 x0_register_input_tail_127.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma x0_register_input_nonregister_127 : has_register 127 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem x0_register_input_connection_127 invalid old current result source_value value :
 VM.find 7760 old = Some source_value ->
 adapt_hvalue_as_type source_value (Gtyp (Fuint 1)) = Some value ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 127 result = Some value.
Proof.
 intros Source Adapt Step.
 exact (declared_connection_value 104 flat_statements x0_register_input_decl_127 x0_register_input_mid_127 x0_register_input_tail_127
 127 7760 1 source_value value invalid flat_memories old current result
 x0_register_input_position_127 x0_register_input_split_127 x0_register_input_straight_127 x0_register_input_mid_safe_127 x0_register_input_tail_safe_127
 x0_register_input_nonregister_127 (Logic.eq_refl _) Source Adapt Step).
Qed.
Theorem x0_register_input_concrete_127 invalid old current result width bits :
 VM.find 7760 old = Some (Gval (Fuint width) bits) ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 exists word, VM.find 127 result = Some (Gval (Fuint 1) word).
Proof.
 intros Source Step. eexists.
 eapply x0_register_input_connection_127; [exact Source|reflexivity|exact Step].
Qed.
Definition x0_register_input_decl_124 := match straight_drop 102 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition x0_register_input_tail_124 := match straight_drop 8792 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition x0_register_input_mid_124 := take_statements 8689 x0_register_input_decl_124.
Lemma x0_register_input_position_124 : straight_drop 101 flat_statements = Some (@Qcons VarOrder.T (@Swire VarOrder.T 124 (Gtyp (Fuint 1))) x0_register_input_decl_124).
Proof. vm_compute. reflexivity. Qed.
Lemma x0_register_input_split_124 : x0_register_input_decl_124 = statement_append x0_register_input_mid_124 (@Qcons VarOrder.T (@Sfcnct VarOrder.T (@Eid VarOrder.T 124) (@Eref VarOrder.T (@Eid VarOrder.T 7759))) x0_register_input_tail_124).
Proof. vm_compute. reflexivity. Qed.
Lemma x0_register_input_straight_124 : straight_statements x0_register_input_mid_124.
Proof. vm_compute. exact I. Qed.
Lemma x0_register_input_mid_safe_124 : formal_typed_suffix_safe flat_memories 124 x0_register_input_mid_124.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma x0_register_input_tail_safe_124 : formal_typed_suffix_safe flat_memories 124 x0_register_input_tail_124.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma x0_register_input_nonregister_124 : has_register 124 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem x0_register_input_connection_124 invalid old current result source_value value :
 VM.find 7759 old = Some source_value ->
 adapt_hvalue_as_type source_value (Gtyp (Fuint 1)) = Some value ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 124 result = Some value.
Proof.
 intros Source Adapt Step.
 exact (declared_connection_value 101 flat_statements x0_register_input_decl_124 x0_register_input_mid_124 x0_register_input_tail_124
 124 7759 1 source_value value invalid flat_memories old current result
 x0_register_input_position_124 x0_register_input_split_124 x0_register_input_straight_124 x0_register_input_mid_safe_124 x0_register_input_tail_safe_124
 x0_register_input_nonregister_124 (Logic.eq_refl _) Source Adapt Step).
Qed.
Theorem x0_register_input_concrete_124 invalid old current result width bits :
 VM.find 7759 old = Some (Gval (Fuint width) bits) ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 exists word, VM.find 124 result = Some (Gval (Fuint 1) word).
Proof.
 intros Source Step. eexists.
 eapply x0_register_input_connection_124; [exact Source|reflexivity|exact Step].
Qed.
Definition x0_register_input_decl_126 := match straight_drop 104 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition x0_register_input_tail_126 := match straight_drop 8794 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition x0_register_input_mid_126 := take_statements 8689 x0_register_input_decl_126.
Lemma x0_register_input_position_126 : straight_drop 103 flat_statements = Some (@Qcons VarOrder.T (@Swire VarOrder.T 126 (Gtyp (Fuint 3))) x0_register_input_decl_126).
Proof. vm_compute. reflexivity. Qed.
Lemma x0_register_input_split_126 : x0_register_input_decl_126 = statement_append x0_register_input_mid_126 (@Qcons VarOrder.T (@Sfcnct VarOrder.T (@Eid VarOrder.T 126) (@Eref VarOrder.T (@Eid VarOrder.T 7755))) x0_register_input_tail_126).
Proof. vm_compute. reflexivity. Qed.
Lemma x0_register_input_straight_126 : straight_statements x0_register_input_mid_126.
Proof. vm_compute. exact I. Qed.
Lemma x0_register_input_mid_safe_126 : formal_typed_suffix_safe flat_memories 126 x0_register_input_mid_126.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma x0_register_input_tail_safe_126 : formal_typed_suffix_safe flat_memories 126 x0_register_input_tail_126.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma x0_register_input_nonregister_126 : has_register 126 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem x0_register_input_connection_126 invalid old current result source_value value :
 VM.find 7755 old = Some source_value ->
 adapt_hvalue_as_type source_value (Gtyp (Fuint 3)) = Some value ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 126 result = Some value.
Proof.
 intros Source Adapt Step.
 exact (declared_connection_value 103 flat_statements x0_register_input_decl_126 x0_register_input_mid_126 x0_register_input_tail_126
 126 7755 3 source_value value invalid flat_memories old current result
 x0_register_input_position_126 x0_register_input_split_126 x0_register_input_straight_126 x0_register_input_mid_safe_126 x0_register_input_tail_safe_126
 x0_register_input_nonregister_126 (Logic.eq_refl _) Source Adapt Step).
Qed.
Theorem x0_register_input_concrete_126 invalid old current result width bits :
 VM.find 7755 old = Some (Gval (Fuint width) bits) ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 exists word, VM.find 126 result = Some (Gval (Fuint 3) word).
Proof.
 intros Source Step. eexists.
 eapply x0_register_input_connection_126; [exact Source|reflexivity|exact Step].
Qed.
Definition x0_register_input_decl_125 := match straight_drop 103 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition x0_register_input_tail_125 := match straight_drop 8793 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition x0_register_input_mid_125 := take_statements 8689 x0_register_input_decl_125.
Lemma x0_register_input_position_125 : straight_drop 102 flat_statements = Some (@Qcons VarOrder.T (@Swire VarOrder.T 125 (Gtyp (Fuint 2))) x0_register_input_decl_125).
Proof. vm_compute. reflexivity. Qed.
Lemma x0_register_input_split_125 : x0_register_input_decl_125 = statement_append x0_register_input_mid_125 (@Qcons VarOrder.T (@Sfcnct VarOrder.T (@Eid VarOrder.T 125) (@Eref VarOrder.T (@Eid VarOrder.T 7754))) x0_register_input_tail_125).
Proof. vm_compute. reflexivity. Qed.
Lemma x0_register_input_straight_125 : straight_statements x0_register_input_mid_125.
Proof. vm_compute. exact I. Qed.
Lemma x0_register_input_mid_safe_125 : formal_typed_suffix_safe flat_memories 125 x0_register_input_mid_125.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma x0_register_input_tail_safe_125 : formal_typed_suffix_safe flat_memories 125 x0_register_input_tail_125.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma x0_register_input_nonregister_125 : has_register 125 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem x0_register_input_connection_125 invalid old current result source_value value :
 VM.find 7754 old = Some source_value ->
 adapt_hvalue_as_type source_value (Gtyp (Fuint 2)) = Some value ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 125 result = Some value.
Proof.
 intros Source Adapt Step.
 exact (declared_connection_value 102 flat_statements x0_register_input_decl_125 x0_register_input_mid_125 x0_register_input_tail_125
 125 7754 2 source_value value invalid flat_memories old current result
 x0_register_input_position_125 x0_register_input_split_125 x0_register_input_straight_125 x0_register_input_mid_safe_125 x0_register_input_tail_safe_125
 x0_register_input_nonregister_125 (Logic.eq_refl _) Source Adapt Step).
Qed.
Theorem x0_register_input_concrete_125 invalid old current result width bits :
 VM.find 7754 old = Some (Gval (Fuint width) bits) ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 exists word, VM.find 125 result = Some (Gval (Fuint 2) word).
Proof.
 intros Source Step. eexists.
 eapply x0_register_input_connection_125; [exact Source|reflexivity|exact Step].
Qed.
Print Assumptions x0_register_input_concrete_125.
