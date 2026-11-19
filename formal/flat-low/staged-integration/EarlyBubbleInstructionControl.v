Require Import CoreSocModel ComparisonNodes FormalNodeEquation MemorySuffixCertificates MemoryWriteFrames ScalarNodeFrames RegisterInvariants.
From Coq Require Import ZArith.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths Firrtl_with_implicit_widths HiEnv_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Definition bubble_instruction_expr_7794 := (@Eprim_binop VarOrder.T Bor (@Eref VarOrder.T (@Eid VarOrder.T 7762)) (@Eref VarOrder.T (@Eid VarOrder.T 85))).
Definition bubble_instruction_tail_7794 := match straight_drop 8301 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma bubble_instruction_position_7794 : straight_drop 8300 flat_statements = Some (@Qcons VarOrder.T (@Snode VarOrder.T 7794 bubble_instruction_expr_7794) bubble_instruction_tail_7794).
Proof. vm_compute. reflexivity. Qed.
Lemma bubble_instruction_suffix_7794 : memory_suffix_safe flat_memories 7794 bubble_instruction_tail_7794.
Proof. apply memory_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma bubble_instruction_nonregister_7794 : has_register 7794 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem bubble_instruction_equation_7794 invalid old current result :
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 7794 result = eval_hfexpr_with_memory flat_memories bubble_instruction_expr_7794 old old.
Proof.
 intro Step. exact (formal_combinational_node_equation _ _ _ _ _ invalid flat_memories old current result
 bubble_instruction_position_7794 bubble_instruction_suffix_7794 bubble_instruction_nonregister_7794 Step).
Qed.
Definition bubble_instruction_expr_7795 := (@Eprim_binop VarOrder.T Bor (@Eref VarOrder.T (@Eid VarOrder.T 7794)) (@Eref VarOrder.T (@Eid VarOrder.T 1360))).
Definition bubble_instruction_tail_7795 := match straight_drop 8302 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma bubble_instruction_position_7795 : straight_drop 8301 flat_statements = Some (@Qcons VarOrder.T (@Snode VarOrder.T 7795 bubble_instruction_expr_7795) bubble_instruction_tail_7795).
Proof. vm_compute. reflexivity. Qed.
Lemma bubble_instruction_suffix_7795 : memory_suffix_safe flat_memories 7795 bubble_instruction_tail_7795.
Proof. apply memory_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma bubble_instruction_nonregister_7795 : has_register 7795 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem bubble_instruction_equation_7795 invalid old current result :
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 7795 result = eval_hfexpr_with_memory flat_memories bubble_instruction_expr_7795 old old.
Proof.
 intro Step. exact (formal_combinational_node_equation _ _ _ _ _ invalid flat_memories old current result
 bubble_instruction_position_7795 bubble_instruction_suffix_7795 bubble_instruction_nonregister_7795 Step).
Qed.
Definition bubble_instruction_expr_7796 := (@Eprim_binop VarOrder.T Bor (@Eref VarOrder.T (@Eid VarOrder.T 7795)) (@Eref VarOrder.T (@Eid VarOrder.T 128))).
Definition bubble_instruction_tail_7796 := match straight_drop 8303 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma bubble_instruction_position_7796 : straight_drop 8302 flat_statements = Some (@Qcons VarOrder.T (@Snode VarOrder.T 7796 bubble_instruction_expr_7796) bubble_instruction_tail_7796).
Proof. vm_compute. reflexivity. Qed.
Lemma bubble_instruction_suffix_7796 : memory_suffix_safe flat_memories 7796 bubble_instruction_tail_7796.
Proof. apply memory_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma bubble_instruction_nonregister_7796 : has_register 7796 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem bubble_instruction_equation_7796 invalid old current result :
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 7796 result = eval_hfexpr_with_memory flat_memories bubble_instruction_expr_7796 old old.
Proof.
 intro Step. exact (formal_combinational_node_equation _ _ _ _ _ invalid flat_memories old current result
 bubble_instruction_position_7796 bubble_instruction_suffix_7796 bubble_instruction_nonregister_7796 Step).
Qed.
Definition bubble_instruction_expr_7942 := (@Eprim_binop VarOrder.T Bor (@Eref VarOrder.T (@Eid VarOrder.T 7762)) (@Eref VarOrder.T (@Eid VarOrder.T 85))).
Definition bubble_instruction_tail_7942 := match straight_drop 8449 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma bubble_instruction_position_7942 : straight_drop 8448 flat_statements = Some (@Qcons VarOrder.T (@Snode VarOrder.T 7942 bubble_instruction_expr_7942) bubble_instruction_tail_7942).
Proof. vm_compute. reflexivity. Qed.
Lemma bubble_instruction_suffix_7942 : memory_suffix_safe flat_memories 7942 bubble_instruction_tail_7942.
Proof. apply memory_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma bubble_instruction_nonregister_7942 : has_register 7942 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem bubble_instruction_equation_7942 invalid old current result :
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 7942 result = eval_hfexpr_with_memory flat_memories bubble_instruction_expr_7942 old old.
Proof.
 intro Step. exact (formal_combinational_node_equation _ _ _ _ _ invalid flat_memories old current result
 bubble_instruction_position_7942 bubble_instruction_suffix_7942 bubble_instruction_nonregister_7942 Step).
Qed.
Definition bubble_instruction_expr_7943 := (@Eprim_binop VarOrder.T Bor (@Eref VarOrder.T (@Eid VarOrder.T 7942)) (@Eref VarOrder.T (@Eid VarOrder.T 1360))).
Definition bubble_instruction_tail_7943 := match straight_drop 8450 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma bubble_instruction_position_7943 : straight_drop 8449 flat_statements = Some (@Qcons VarOrder.T (@Snode VarOrder.T 7943 bubble_instruction_expr_7943) bubble_instruction_tail_7943).
Proof. vm_compute. reflexivity. Qed.
Lemma bubble_instruction_suffix_7943 : memory_suffix_safe flat_memories 7943 bubble_instruction_tail_7943.
Proof. apply memory_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma bubble_instruction_nonregister_7943 : has_register 7943 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem bubble_instruction_equation_7943 invalid old current result :
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 7943 result = eval_hfexpr_with_memory flat_memories bubble_instruction_expr_7943 old old.
Proof.
 intro Step. exact (formal_combinational_node_equation _ _ _ _ _ invalid flat_memories old current result
 bubble_instruction_position_7943 bubble_instruction_suffix_7943 bubble_instruction_nonregister_7943 Step).
Qed.
Definition bubble_instruction_expr_7944 := (@Eprim_binop VarOrder.T Bor (@Eref VarOrder.T (@Eid VarOrder.T 7943)) (@Eref VarOrder.T (@Eid VarOrder.T 128))).
Definition bubble_instruction_tail_7944 := match straight_drop 8451 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma bubble_instruction_position_7944 : straight_drop 8450 flat_statements = Some (@Qcons VarOrder.T (@Snode VarOrder.T 7944 bubble_instruction_expr_7944) bubble_instruction_tail_7944).
Proof. vm_compute. reflexivity. Qed.
Lemma bubble_instruction_suffix_7944 : memory_suffix_safe flat_memories 7944 bubble_instruction_tail_7944.
Proof. apply memory_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma bubble_instruction_nonregister_7944 : has_register 7944 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem bubble_instruction_equation_7944 invalid old current result :
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 7944 result = eval_hfexpr_with_memory flat_memories bubble_instruction_expr_7944 old old.
Proof.
 intro Step. exact (formal_combinational_node_equation _ _ _ _ _ invalid flat_memories old current result
 bubble_instruction_position_7944 bubble_instruction_suffix_7944 bubble_instruction_nonregister_7944 Step).
Qed.
Theorem early_bubble_instruction_control_after_three invalid s0 s1 s2 s3 :
 formal_value_iter invalid flat_memories s0 false s0 flat_statements = Some s1 ->
 formal_value_iter invalid flat_memories s1 false s1 flat_statements = Some s2 ->
 formal_value_iter invalid flat_memories s2 false s2 flat_statements = Some s3 ->
 VM.find 7944 s3 = VM.find 7796 s3.
Proof.
 intros S1 S2 S3.
 assert (A : VM.find 7942 s1 = VM.find 7794 s1).
 { rewrite (bubble_instruction_equation_7942 invalid s0 s0 s1 S1)
   (bubble_instruction_equation_7794 invalid s0 s0 s1 S1). reflexivity. }
 assert (B : VM.find 7943 s2 = VM.find 7795 s2).
 { rewrite (bubble_instruction_equation_7943 invalid s1 s1 s2 S2)
   (bubble_instruction_equation_7795 invalid s1 s1 s2 S2).
   cbn [bubble_instruction_expr_7943 bubble_instruction_expr_7795 eval_hfexpr_with_memory eval_href_with_memory].
   rewrite A. reflexivity. }
 rewrite (bubble_instruction_equation_7944 invalid s2 s2 s3 S3)
 (bubble_instruction_equation_7796 invalid s2 s2 s3 S3).
 cbn [bubble_instruction_expr_7944 bubble_instruction_expr_7796 eval_hfexpr_with_memory eval_href_with_memory].
 rewrite B. reflexivity.
Qed.
Print Assumptions early_bubble_instruction_control_after_three.
