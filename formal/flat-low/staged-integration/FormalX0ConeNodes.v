Require Import FormalNodeEquation RegisterInvariants CoreSocModel ComparisonNodes ScalarNodeFrames MemoryWriteFrames MemorySuffixCertificates.
From Coq Require Import ZArith.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths Firrtl_with_implicit_widths HiEnv_with_implicit_widths
 HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Definition expr_953 := (@Eprim_unop VarOrder.T Uorr (@Eref VarOrder.T (@Eid VarOrder.T 785))).
Definition tail_953 := match straight_drop 963 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma position_953 : straight_drop 962 flat_statements = Some (@Qcons VarOrder.T (@Snode VarOrder.T 953 expr_953) tail_953).
Proof. vm_compute. reflexivity. Qed.
Lemma suffix_953 : memory_suffix_safe flat_memories 953 tail_953.
Proof. apply memory_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma nonregister_953 : has_register 953 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem node_953_full_iteration invalid old current result :
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 953 result = eval_hfexpr_with_memory flat_memories expr_953 old old.
Proof. intro Step. exact (formal_combinational_node_equation _ _ _ _ _ invalid flat_memories old current result position_953 suffix_953 nonregister_953 Step). Qed.
Definition expr_954 := (@Eprim_binop VarOrder.T Band (@Eref VarOrder.T (@Eid VarOrder.T 784)) (@Eref VarOrder.T (@Eid VarOrder.T 953))).
Definition tail_954 := match straight_drop 964 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma position_954 : straight_drop 963 flat_statements = Some (@Qcons VarOrder.T (@Snode VarOrder.T 954 expr_954) tail_954).
Proof. vm_compute. reflexivity. Qed.
Lemma suffix_954 : memory_suffix_safe flat_memories 954 tail_954.
Proof. apply memory_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma nonregister_954 : has_register 954 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem node_954_full_iteration invalid old current result :
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 954 result = eval_hfexpr_with_memory flat_memories expr_954 old old.
Proof. intro Step. exact (formal_combinational_node_equation _ _ _ _ _ invalid flat_memories old current result position_954 suffix_954 nonregister_954 Step). Qed.
Definition expr_989 := (@Emux VarOrder.T (@Eprim_binop VarOrder.T (Bcomp Beq) (@Econst VarOrder.T (Fuint 1) [::false]) (@Eref VarOrder.T (@Eid VarOrder.T 785))) (@Eref VarOrder.T (@Eid VarOrder.T 988)) (@Econst VarOrder.T (Fuint 1) [::false])).
Definition tail_989 := match straight_drop 999 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma position_989 : straight_drop 998 flat_statements = Some (@Qcons VarOrder.T (@Snode VarOrder.T 989 expr_989) tail_989).
Proof. vm_compute. reflexivity. Qed.
Lemma suffix_989 : memory_suffix_safe flat_memories 989 tail_989.
Proof. apply memory_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma nonregister_989 : has_register 989 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem node_989_full_iteration invalid old current result :
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 989 result = eval_hfexpr_with_memory flat_memories expr_989 old old.
Proof. intro Step. exact (formal_combinational_node_equation _ _ _ _ _ invalid flat_memories old current result position_989 suffix_989 nonregister_989 Step). Qed.
Definition expr_1053 := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 954)) (@Eref VarOrder.T (@Eid VarOrder.T 989)) (@Econst VarOrder.T (Fuint 1) [::false])).
Definition tail_1053 := match straight_drop 1063 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma position_1053 : straight_drop 1062 flat_statements = Some (@Qcons VarOrder.T (@Snode VarOrder.T 1053 expr_1053) tail_1053).
Proof. vm_compute. reflexivity. Qed.
Lemma suffix_1053 : memory_suffix_safe flat_memories 1053 tail_1053.
Proof. apply memory_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma nonregister_1053 : has_register 1053 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem node_1053_full_iteration invalid old current result :
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 1053 result = eval_hfexpr_with_memory flat_memories expr_1053 old old.
Proof. intro Step. exact (formal_combinational_node_equation _ _ _ _ _ invalid flat_memories old current result position_1053 suffix_1053 nonregister_1053 Step). Qed.
Print Assumptions node_1053_full_iteration.
