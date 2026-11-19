Require Import CoreSocModel ComparisonNodes FormalNodeEquation FormalTypedNodeEquation FormalTypedNodeFrames MemorySuffixCertificates MemoryWriteFrames ScalarNodeFrames RegisterInvariants.
From Coq Require Import ZArith.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths Firrtl_with_implicit_widths HiEnv_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Definition legal_expr_9139 := (@Eprim_binop VarOrder.T Bor (@Eref VarOrder.T (@Eid VarOrder.T 9028)) (@Eref VarOrder.T (@Eid VarOrder.T 9138))).
Definition legal_tail_9139 := match straight_drop 9913 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma legal_position_9139 : straight_drop 9912 flat_statements = Some (@Qcons VarOrder.T (@Snode VarOrder.T 9139 legal_expr_9139) legal_tail_9139).
Proof. vm_compute. reflexivity. Qed.
Lemma legal_suffix_9139 : memory_suffix_safe flat_memories 9139 legal_tail_9139.
Proof. apply memory_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma legal_nonregister_9139 : has_register 9139 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem legal_equation_9139 invalid old current result :
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 9139 result = eval_hfexpr_with_memory flat_memories legal_expr_9139 old old.
Proof.
 intro Step. exact (formal_combinational_node_equation _ _ _ _ _ invalid flat_memories old current result
 legal_position_9139 legal_suffix_9139 legal_nonregister_9139 Step).
Qed.
Definition legal_expr_9140 := (@Eprim_binop VarOrder.T (Bcomp Beq) (@Eref VarOrder.T (@Eid VarOrder.T 45)) (@Econst VarOrder.T (Fuint 1) [::false])).
Definition legal_tail_9140 := match straight_drop 9914 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma legal_position_9140 : straight_drop 9913 flat_statements = Some (@Qcons VarOrder.T (@Snode VarOrder.T 9140 legal_expr_9140) legal_tail_9140).
Proof. vm_compute. reflexivity. Qed.
Lemma legal_suffix_9140 : memory_suffix_safe flat_memories 9140 legal_tail_9140.
Proof. apply memory_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma legal_nonregister_9140 : has_register 9140 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem legal_equation_9140 invalid old current result :
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 9140 result = eval_hfexpr_with_memory flat_memories legal_expr_9140 old old.
Proof.
 intro Step. exact (formal_combinational_node_equation _ _ _ _ _ invalid flat_memories old current result
 legal_position_9140 legal_suffix_9140 legal_nonregister_9140 Step).
Qed.
Definition legal_expr_9141 := (@Eprim_binop VarOrder.T Band (@Eref VarOrder.T (@Eid VarOrder.T 9139)) (@Eref VarOrder.T (@Eid VarOrder.T 9140))).
Definition legal_tail_9141 := match straight_drop 9915 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma legal_position_9141 : straight_drop 9914 flat_statements = Some (@Qcons VarOrder.T (@Snode VarOrder.T 9141 legal_expr_9141) legal_tail_9141).
Proof. vm_compute. reflexivity. Qed.
Lemma legal_suffix_9141 : formal_typed_suffix_safe flat_memories 9141 legal_tail_9141.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma legal_nonregister_9141 : has_register 9141 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem legal_value_9141 invalid old current result value :
 eval_hfexpr_with_memory flat_memories legal_expr_9141 old old = Some value ->
 type_of_val value = Gtyp (Fuint 1) ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 9141 result = Some value.
Proof.
 intros Eval Typed Step. eapply formal_combinational_known_node;
 [exact legal_position_9141|exact legal_suffix_9141|exact legal_nonregister_9141|exact Eval|exact Typed|exact Step].
Qed.
Definition legal_expr_9153 := (@Eref VarOrder.T (@Eid VarOrder.T 100)).
Definition legal_tail_9153 := match straight_drop 9927 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma legal_position_9153 : straight_drop 9926 flat_statements = Some (@Qcons VarOrder.T (@Snode VarOrder.T 9153 legal_expr_9153) legal_tail_9153).
Proof. vm_compute. reflexivity. Qed.
Lemma legal_suffix_9153 : memory_suffix_safe flat_memories 9153 legal_tail_9153.
Proof. apply memory_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma legal_nonregister_9153 : has_register 9153 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem legal_equation_9153 invalid old current result :
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 9153 result = eval_hfexpr_with_memory flat_memories legal_expr_9153 old old.
Proof.
 intro Step. exact (formal_combinational_node_equation _ _ _ _ _ invalid flat_memories old current result
 legal_position_9153 legal_suffix_9153 legal_nonregister_9153 Step).
Qed.
Definition legal_expr_9157 := (@Eref VarOrder.T (@Eid VarOrder.T 9153)).
Definition legal_tail_9157 := match straight_drop 9931 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma legal_position_9157 : straight_drop 9930 flat_statements = Some (@Qcons VarOrder.T (@Snode VarOrder.T 9157 legal_expr_9157) legal_tail_9157).
Proof. vm_compute. reflexivity. Qed.
Lemma legal_suffix_9157 : formal_typed_suffix_safe flat_memories 9157 legal_tail_9157.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma legal_nonregister_9157 : has_register 9157 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem legal_value_9157 invalid old current result value :
 eval_hfexpr_with_memory flat_memories legal_expr_9157 old old = Some value ->
 type_of_val value = Gtyp (Fuint 1) ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 9157 result = Some value.
Proof.
 intros Eval Typed Step. eapply formal_combinational_known_node;
 [exact legal_position_9157|exact legal_suffix_9157|exact legal_nonregister_9157|exact Eval|exact Typed|exact Step].
Qed.
Definition legal_expr_9237 := (@Eprim_unop VarOrder.T (Uextr 0 0) (@Eref VarOrder.T (@Eid VarOrder.T 1))).
Definition legal_tail_9237 := match straight_drop 10067 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma legal_position_9237 : straight_drop 10066 flat_statements = Some (@Qcons VarOrder.T (@Snode VarOrder.T 9237 legal_expr_9237) legal_tail_9237).
Proof. vm_compute. reflexivity. Qed.
Lemma legal_suffix_9237 : memory_suffix_safe flat_memories 9237 legal_tail_9237.
Proof. apply memory_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma legal_nonregister_9237 : has_register 9237 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem legal_equation_9237 invalid old current result :
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 9237 result = eval_hfexpr_with_memory flat_memories legal_expr_9237 old old.
Proof.
 intro Step. exact (formal_combinational_node_equation _ _ _ _ _ invalid flat_memories old current result
 legal_position_9237 legal_suffix_9237 legal_nonregister_9237 Step).
Qed.
Definition legal_expr_9238 := (@Eprim_binop VarOrder.T (Bcomp Beq) (@Eref VarOrder.T (@Eid VarOrder.T 9237)) (@Econst VarOrder.T (Fuint 1) [::false])).
Definition legal_tail_9238 := match straight_drop 10068 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma legal_position_9238 : straight_drop 10067 flat_statements = Some (@Qcons VarOrder.T (@Snode VarOrder.T 9238 legal_expr_9238) legal_tail_9238).
Proof. vm_compute. reflexivity. Qed.
Lemma legal_suffix_9238 : memory_suffix_safe flat_memories 9238 legal_tail_9238.
Proof. apply memory_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma legal_nonregister_9238 : has_register 9238 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem legal_equation_9238 invalid old current result :
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 9238 result = eval_hfexpr_with_memory flat_memories legal_expr_9238 old old.
Proof.
 intro Step. exact (formal_combinational_node_equation _ _ _ _ _ invalid flat_memories old current result
 legal_position_9238 legal_suffix_9238 legal_nonregister_9238 Step).
Qed.
Definition legal_expr_9239 := (@Eref VarOrder.T (@Eid VarOrder.T 63)).
Definition legal_tail_9239 := match straight_drop 10069 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma legal_position_9239 : straight_drop 10068 flat_statements = Some (@Qcons VarOrder.T (@Snode VarOrder.T 9239 legal_expr_9239) legal_tail_9239).
Proof. vm_compute. reflexivity. Qed.
Lemma legal_suffix_9239 : memory_suffix_safe flat_memories 9239 legal_tail_9239.
Proof. apply memory_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma legal_nonregister_9239 : has_register 9239 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem legal_equation_9239 invalid old current result :
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 9239 result = eval_hfexpr_with_memory flat_memories legal_expr_9239 old old.
Proof.
 intro Step. exact (formal_combinational_node_equation _ _ _ _ _ invalid flat_memories old current result
 legal_position_9239 legal_suffix_9239 legal_nonregister_9239 Step).
Qed.
Definition legal_expr_9240 := (@Eref VarOrder.T (@Eid VarOrder.T 9239)).
Definition legal_tail_9240 := match straight_drop 10070 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma legal_position_9240 : straight_drop 10069 flat_statements = Some (@Qcons VarOrder.T (@Snode VarOrder.T 9240 legal_expr_9240) legal_tail_9240).
Proof. vm_compute. reflexivity. Qed.
Lemma legal_suffix_9240 : memory_suffix_safe flat_memories 9240 legal_tail_9240.
Proof. apply memory_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma legal_nonregister_9240 : has_register 9240 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem legal_equation_9240 invalid old current result :
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 9240 result = eval_hfexpr_with_memory flat_memories legal_expr_9240 old old.
Proof.
 intro Step. exact (formal_combinational_node_equation _ _ _ _ _ invalid flat_memories old current result
 legal_position_9240 legal_suffix_9240 legal_nonregister_9240 Step).
Qed.
Print Assumptions legal_equation_9240.
