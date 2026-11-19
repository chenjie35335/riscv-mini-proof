Require Import RegisterInvariants CoreSocModel ComparisonNodes ScalarNodeFrames FormalTypedNodeFrames FormalTypedNodeEquation.
From Coq Require Import ZArith.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths Firrtl_with_implicit_widths HiEnv_with_implicit_widths
 HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Definition rf_source_expr_954 := (@Eprim_binop VarOrder.T Band (@Eref VarOrder.T (@Eid VarOrder.T 784)) (@Eref VarOrder.T (@Eid VarOrder.T 953))).
Definition rf_source_tail_954 := match straight_drop 964 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma rf_source_position_954 : straight_drop 963 flat_statements = Some (@Qcons VarOrder.T (@Snode VarOrder.T 954 rf_source_expr_954) rf_source_tail_954).
Proof. vm_compute. reflexivity. Qed.
Lemma rf_source_suffix_954 : formal_typed_suffix_safe flat_memories 954 rf_source_tail_954.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma rf_source_nonregister_954 : has_register 954 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem rf_source_node_954 invalid old current result value :
 eval_hfexpr_with_memory flat_memories rf_source_expr_954 old old = Some value ->
 type_of_val value = Gtyp (Fuint 1) ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 954 result = Some value.
Proof. intros Eval Typed Step. eapply formal_combinational_known_node;
 [exact rf_source_position_954|exact rf_source_suffix_954|exact rf_source_nonregister_954|exact Eval|exact Typed|exact Step]. Qed.
Definition rf_source_expr_955 := (@Eref VarOrder.T (@Eid VarOrder.T 786)).
Definition rf_source_tail_955 := match straight_drop 965 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma rf_source_position_955 : straight_drop 964 flat_statements = Some (@Qcons VarOrder.T (@Snode VarOrder.T 955 rf_source_expr_955) rf_source_tail_955).
Proof. vm_compute. reflexivity. Qed.
Lemma rf_source_suffix_955 : formal_typed_suffix_safe flat_memories 955 rf_source_tail_955.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma rf_source_nonregister_955 : has_register 955 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem rf_source_node_955 invalid old current result value :
 eval_hfexpr_with_memory flat_memories rf_source_expr_955 old old = Some value ->
 type_of_val value = Gtyp (Fuint 32) ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 955 result = Some value.
Proof. intros Eval Typed Step. eapply formal_combinational_known_node;
 [exact rf_source_position_955|exact rf_source_suffix_955|exact rf_source_nonregister_955|exact Eval|exact Typed|exact Step]. Qed.
Definition rf_source_expr_957 := (@Emux VarOrder.T (@Eprim_binop VarOrder.T (Bcomp Beq) (@Econst VarOrder.T (Fuint 1) [::true]) (@Eref VarOrder.T (@Eid VarOrder.T 785))) (@Eref VarOrder.T (@Eid VarOrder.T 955)) (@Eref VarOrder.T (@Eid VarOrder.T 852))).
Definition rf_source_tail_957 := match straight_drop 967 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma rf_source_position_957 : straight_drop 966 flat_statements = Some (@Qcons VarOrder.T (@Snode VarOrder.T 957 rf_source_expr_957) rf_source_tail_957).
Proof. vm_compute. reflexivity. Qed.
Lemma rf_source_suffix_957 : formal_typed_suffix_safe flat_memories 957 rf_source_tail_957.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma rf_source_nonregister_957 : has_register 957 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem rf_source_node_957 invalid old current result value :
 eval_hfexpr_with_memory flat_memories rf_source_expr_957 old old = Some value ->
 type_of_val value = Gtyp (Fuint 32) ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 957 result = Some value.
Proof. intros Eval Typed Step. eapply formal_combinational_known_node;
 [exact rf_source_position_957|exact rf_source_suffix_957|exact rf_source_nonregister_957|exact Eval|exact Typed|exact Step]. Qed.
Definition rf_source_expr_1022 := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 954)) (@Eref VarOrder.T (@Eid VarOrder.T 957)) (@Eref VarOrder.T (@Eid VarOrder.T 852))).
Definition rf_source_tail_1022 := match straight_drop 1032 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma rf_source_position_1022 : straight_drop 1031 flat_statements = Some (@Qcons VarOrder.T (@Snode VarOrder.T 1022 rf_source_expr_1022) rf_source_tail_1022).
Proof. vm_compute. reflexivity. Qed.
Lemma rf_source_suffix_1022 : formal_typed_suffix_safe flat_memories 1022 rf_source_tail_1022.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma rf_source_nonregister_1022 : has_register 1022 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem rf_source_node_1022 invalid old current result value :
 eval_hfexpr_with_memory flat_memories rf_source_expr_1022 old old = Some value ->
 type_of_val value = Gtyp (Fuint 32) ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 1022 result = Some value.
Proof. intros Eval Typed Step. eapply formal_combinational_known_node;
 [exact rf_source_position_1022|exact rf_source_suffix_1022|exact rf_source_nonregister_1022|exact Eval|exact Typed|exact Step]. Qed.
Print Assumptions rf_source_node_1022.
