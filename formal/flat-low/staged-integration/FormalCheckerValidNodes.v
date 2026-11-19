Require Import CoreSocModel ComparisonNodes FormalNodeEquation MemorySuffixCertificates MemoryWriteFrames ScalarNodeFrames RegisterInvariants.
From Coq Require Import ZArith.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths Firrtl_with_implicit_widths HiEnv_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Definition checker_valid_expr_7948 := (@Eprim_binop VarOrder.T Bor (@Eref VarOrder.T (@Eid VarOrder.T 7947)) (@Eref VarOrder.T (@Eid VarOrder.T 7765))).
Definition checker_valid_tail_7948 := match straight_drop 8455 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma checker_valid_position_7948 : straight_drop 8454 flat_statements = Some (@Qcons VarOrder.T (@Snode VarOrder.T 7948 checker_valid_expr_7948) checker_valid_tail_7948).
Proof. vm_compute. reflexivity. Qed.
Lemma checker_valid_suffix_7948 : memory_suffix_safe flat_memories 7948 checker_valid_tail_7948.
Proof. apply memory_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma checker_valid_nonregister_7948 : has_register 7948 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem checker_valid_equation_7948 invalid old current result :
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 7948 result = eval_hfexpr_with_memory flat_memories checker_valid_expr_7948 old old.
Proof.
 intro Step. exact (formal_combinational_node_equation _ _ _ _ _ invalid flat_memories old current result
 checker_valid_position_7948 checker_valid_suffix_7948 checker_valid_nonregister_7948 Step).
Qed.
Lemma checker_valid_congruent_7948 invalid left right next_left next_right :
 VM.find 7947 left = VM.find 7947 right ->
 VM.find 7765 left = VM.find 7765 right ->
 formal_value_iter invalid flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter invalid flat_memories right false right flat_statements = Some next_right ->
 VM.find 7948 next_left = VM.find 7948 next_right.
Proof. intros H0 H1 L R.
 rewrite (checker_valid_equation_7948 invalid left left next_left L) (checker_valid_equation_7948 invalid right right next_right R).
 cbn [checker_valid_expr_7948 eval_hfexpr_with_memory eval_href_with_memory].
 rewrite H0 H1. reflexivity. Qed.
Definition checker_valid_expr_7949 := (@Ecast VarOrder.T AsUInt (@Eref VarOrder.T (@Eid VarOrder.T 65))).
Definition checker_valid_tail_7949 := match straight_drop 8456 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma checker_valid_position_7949 : straight_drop 8455 flat_statements = Some (@Qcons VarOrder.T (@Snode VarOrder.T 7949 checker_valid_expr_7949) checker_valid_tail_7949).
Proof. vm_compute. reflexivity. Qed.
Lemma checker_valid_suffix_7949 : memory_suffix_safe flat_memories 7949 checker_valid_tail_7949.
Proof. apply memory_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma checker_valid_nonregister_7949 : has_register 7949 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem checker_valid_equation_7949 invalid old current result :
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 7949 result = eval_hfexpr_with_memory flat_memories checker_valid_expr_7949 old old.
Proof.
 intro Step. exact (formal_combinational_node_equation _ _ _ _ _ invalid flat_memories old current result
 checker_valid_position_7949 checker_valid_suffix_7949 checker_valid_nonregister_7949 Step).
Qed.
Lemma checker_valid_congruent_7949 invalid left right next_left next_right :
 VM.find 65 left = VM.find 65 right ->
 formal_value_iter invalid flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter invalid flat_memories right false right flat_statements = Some next_right ->
 VM.find 7949 next_left = VM.find 7949 next_right.
Proof. intros H0 L R.
 rewrite (checker_valid_equation_7949 invalid left left next_left L) (checker_valid_equation_7949 invalid right right next_right R).
 cbn [checker_valid_expr_7949 eval_hfexpr_with_memory eval_href_with_memory].
 rewrite H0. reflexivity. Qed.
Definition checker_valid_expr_7950 := (@Eprim_binop VarOrder.T Bor (@Eref VarOrder.T (@Eid VarOrder.T 7948)) (@Eref VarOrder.T (@Eid VarOrder.T 7949))).
Definition checker_valid_tail_7950 := match straight_drop 8457 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma checker_valid_position_7950 : straight_drop 8456 flat_statements = Some (@Qcons VarOrder.T (@Snode VarOrder.T 7950 checker_valid_expr_7950) checker_valid_tail_7950).
Proof. vm_compute. reflexivity. Qed.
Lemma checker_valid_suffix_7950 : memory_suffix_safe flat_memories 7950 checker_valid_tail_7950.
Proof. apply memory_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma checker_valid_nonregister_7950 : has_register 7950 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem checker_valid_equation_7950 invalid old current result :
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 7950 result = eval_hfexpr_with_memory flat_memories checker_valid_expr_7950 old old.
Proof.
 intro Step. exact (formal_combinational_node_equation _ _ _ _ _ invalid flat_memories old current result
 checker_valid_position_7950 checker_valid_suffix_7950 checker_valid_nonregister_7950 Step).
Qed.
Lemma checker_valid_congruent_7950 invalid left right next_left next_right :
 VM.find 7948 left = VM.find 7948 right ->
 VM.find 7949 left = VM.find 7949 right ->
 formal_value_iter invalid flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter invalid flat_memories right false right flat_statements = Some next_right ->
 VM.find 7950 next_left = VM.find 7950 next_right.
Proof. intros H0 H1 L R.
 rewrite (checker_valid_equation_7950 invalid left left next_left L) (checker_valid_equation_7950 invalid right right next_right R).
 cbn [checker_valid_expr_7950 eval_hfexpr_with_memory eval_href_with_memory].
 rewrite H0 H1. reflexivity. Qed.
Definition checker_valid_expr_7951 := (@Eref VarOrder.T (@Eid VarOrder.T 7950)).
Definition checker_valid_tail_7951 := match straight_drop 8458 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma checker_valid_position_7951 : straight_drop 8457 flat_statements = Some (@Qcons VarOrder.T (@Snode VarOrder.T 7951 checker_valid_expr_7951) checker_valid_tail_7951).
Proof. vm_compute. reflexivity. Qed.
Lemma checker_valid_suffix_7951 : memory_suffix_safe flat_memories 7951 checker_valid_tail_7951.
Proof. apply memory_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma checker_valid_nonregister_7951 : has_register 7951 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem checker_valid_equation_7951 invalid old current result :
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 7951 result = eval_hfexpr_with_memory flat_memories checker_valid_expr_7951 old old.
Proof.
 intro Step. exact (formal_combinational_node_equation _ _ _ _ _ invalid flat_memories old current result
 checker_valid_position_7951 checker_valid_suffix_7951 checker_valid_nonregister_7951 Step).
Qed.
Lemma checker_valid_congruent_7951 invalid left right next_left next_right :
 VM.find 7950 left = VM.find 7950 right ->
 formal_value_iter invalid flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter invalid flat_memories right false right flat_statements = Some next_right ->
 VM.find 7951 next_left = VM.find 7951 next_right.
Proof. intros H0 L R.
 rewrite (checker_valid_equation_7951 invalid left left next_left L) (checker_valid_equation_7951 invalid right right next_right R).
 cbn [checker_valid_expr_7951 eval_hfexpr_with_memory eval_href_with_memory].
 rewrite H0. reflexivity. Qed.
Definition checker_valid_expr_7952 := (@Eprim_binop VarOrder.T (Bcomp Beq) (@Eref VarOrder.T (@Eid VarOrder.T 7951)) (@Econst VarOrder.T (Fuint 1) [::false])).
Definition checker_valid_tail_7952 := match straight_drop 8459 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma checker_valid_position_7952 : straight_drop 8458 flat_statements = Some (@Qcons VarOrder.T (@Snode VarOrder.T 7952 checker_valid_expr_7952) checker_valid_tail_7952).
Proof. vm_compute. reflexivity. Qed.
Lemma checker_valid_suffix_7952 : memory_suffix_safe flat_memories 7952 checker_valid_tail_7952.
Proof. apply memory_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma checker_valid_nonregister_7952 : has_register 7952 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem checker_valid_equation_7952 invalid old current result :
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 7952 result = eval_hfexpr_with_memory flat_memories checker_valid_expr_7952 old old.
Proof.
 intro Step. exact (formal_combinational_node_equation _ _ _ _ _ invalid flat_memories old current result
 checker_valid_position_7952 checker_valid_suffix_7952 checker_valid_nonregister_7952 Step).
Qed.
Lemma checker_valid_congruent_7952 invalid left right next_left next_right :
 VM.find 7951 left = VM.find 7951 right ->
 formal_value_iter invalid flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter invalid flat_memories right false right flat_statements = Some next_right ->
 VM.find 7952 next_left = VM.find 7952 next_right.
Proof. intros H0 L R.
 rewrite (checker_valid_equation_7952 invalid left left next_left L) (checker_valid_equation_7952 invalid right right next_right R).
 cbn [checker_valid_expr_7952 eval_hfexpr_with_memory eval_href_with_memory].
 rewrite H0. reflexivity. Qed.
Print Assumptions checker_valid_congruent_7952.
