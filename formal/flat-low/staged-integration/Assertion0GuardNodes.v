Require Import CoreSocModel ComparisonNodes FormalNodeEquation FormalTypedNodeEquation FormalTypedNodeFrames MemorySuffixCertificates MemoryWriteFrames ScalarNodeFrames RegisterInvariants.
From Coq Require Import ZArith.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths Firrtl_with_implicit_widths HiEnv_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Definition reference_event_expr_7566 := (@Ecast VarOrder.T AsUInt (@Eref VarOrder.T (@Eid VarOrder.T 1394))).
Definition reference_event_tail_7566 := match straight_drop 8036 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma reference_event_position_7566 : straight_drop 8035 flat_statements = Some (@Qcons VarOrder.T (@Snode VarOrder.T 7566 reference_event_expr_7566) reference_event_tail_7566).
Proof. vm_compute. reflexivity. Qed.
Lemma reference_event_suffix_7566 : memory_suffix_safe flat_memories 7566 reference_event_tail_7566.
Proof. apply memory_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma reference_event_nonregister_7566 : has_register 7566 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem reference_event_equation_7566 invalid old current result :
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 7566 result = eval_hfexpr_with_memory flat_memories reference_event_expr_7566 old old.
Proof.
 intro Step. exact (formal_combinational_node_equation _ _ _ _ _ invalid flat_memories old current result
 reference_event_position_7566 reference_event_suffix_7566 reference_event_nonregister_7566 Step).
Qed.
Definition reference_event_expr_7567 := (@Eprim_binop VarOrder.T (Bcomp Beq) (@Eref VarOrder.T (@Eid VarOrder.T 7566)) (@Econst VarOrder.T (Fuint 1) [::false])).
Definition reference_event_tail_7567 := match straight_drop 8037 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma reference_event_position_7567 : straight_drop 8036 flat_statements = Some (@Qcons VarOrder.T (@Snode VarOrder.T 7567 reference_event_expr_7567) reference_event_tail_7567).
Proof. vm_compute. reflexivity. Qed.
Lemma reference_event_suffix_7567 : memory_suffix_safe flat_memories 7567 reference_event_tail_7567.
Proof. apply memory_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma reference_event_nonregister_7567 : has_register 7567 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem reference_event_equation_7567 invalid old current result :
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 7567 result = eval_hfexpr_with_memory flat_memories reference_event_expr_7567 old old.
Proof.
 intro Step. exact (formal_combinational_node_equation _ _ _ _ _ invalid flat_memories old current result
 reference_event_position_7567 reference_event_suffix_7567 reference_event_nonregister_7567 Step).
Qed.
