Require Import CoreSocModel ComparisonNodes FormalNodeEquation FormalTypedNodeEquation FormalTypedNodeFrames MemorySuffixCertificates MemoryWriteFrames ScalarNodeFrames RegisterInvariants.
From Coq Require Import ZArith.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths Firrtl_with_implicit_widths HiEnv_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Definition reference_event_expr_7575 := (@Ecast VarOrder.T AsUInt (@Eref VarOrder.T (@Eid VarOrder.T 1394))).
Definition reference_event_tail_7575 := match straight_drop 8045 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma reference_event_position_7575 : straight_drop 8044 flat_statements = Some (@Qcons VarOrder.T (@Snode VarOrder.T 7575 reference_event_expr_7575) reference_event_tail_7575).
Proof. vm_compute. reflexivity. Qed.
Lemma reference_event_suffix_7575 : memory_suffix_safe flat_memories 7575 reference_event_tail_7575.
Proof. apply memory_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma reference_event_nonregister_7575 : has_register 7575 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem reference_event_equation_7575 invalid old current result :
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 7575 result = eval_hfexpr_with_memory flat_memories reference_event_expr_7575 old old.
Proof.
 intro Step. exact (formal_combinational_node_equation _ _ _ _ _ invalid flat_memories old current result
 reference_event_position_7575 reference_event_suffix_7575 reference_event_nonregister_7575 Step).
Qed.
Definition reference_event_expr_7576 := (@Eprim_binop VarOrder.T (Bcomp Beq) (@Eref VarOrder.T (@Eid VarOrder.T 7575)) (@Econst VarOrder.T (Fuint 1) [::false])).
Definition reference_event_tail_7576 := match straight_drop 8046 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma reference_event_position_7576 : straight_drop 8045 flat_statements = Some (@Qcons VarOrder.T (@Snode VarOrder.T 7576 reference_event_expr_7576) reference_event_tail_7576).
Proof. vm_compute. reflexivity. Qed.
Lemma reference_event_suffix_7576 : memory_suffix_safe flat_memories 7576 reference_event_tail_7576.
Proof. apply memory_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma reference_event_nonregister_7576 : has_register 7576 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem reference_event_equation_7576 invalid old current result :
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 7576 result = eval_hfexpr_with_memory flat_memories reference_event_expr_7576 old old.
Proof.
 intro Step. exact (formal_combinational_node_equation _ _ _ _ _ invalid flat_memories old current result
 reference_event_position_7576 reference_event_suffix_7576 reference_event_nonregister_7576 Step).
Qed.
Print Assumptions reference_event_equation_7576.
