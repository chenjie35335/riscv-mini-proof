Require Import CoreSocModel ComparisonNodes FormalNodeEquation FormalTypedNodeEquation FormalTypedNodeFrames MemorySuffixCertificates MemoryWriteFrames ScalarNodeFrames RegisterInvariants.
From Coq Require Import ZArith.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths Firrtl_with_implicit_widths HiEnv_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Definition reference_event_expr_7588 := (@Ecast VarOrder.T AsUInt (@Eref VarOrder.T (@Eid VarOrder.T 1394))).
Definition reference_event_tail_7588 := match straight_drop 8058 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma reference_event_position_7588 : straight_drop 8057 flat_statements = Some (@Qcons VarOrder.T (@Snode VarOrder.T 7588 reference_event_expr_7588) reference_event_tail_7588).
Proof. vm_compute. reflexivity. Qed.
Lemma reference_event_suffix_7588 : memory_suffix_safe flat_memories 7588 reference_event_tail_7588.
Proof. apply memory_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma reference_event_nonregister_7588 : has_register 7588 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem reference_event_equation_7588 invalid old current result :
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 7588 result = eval_hfexpr_with_memory flat_memories reference_event_expr_7588 old old.
Proof.
 intro Step. exact (formal_combinational_node_equation _ _ _ _ _ invalid flat_memories old current result
 reference_event_position_7588 reference_event_suffix_7588 reference_event_nonregister_7588 Step).
Qed.
Definition reference_event_expr_7589 := (@Eprim_binop VarOrder.T (Bcomp Beq) (@Eref VarOrder.T (@Eid VarOrder.T 7588)) (@Econst VarOrder.T (Fuint 1) [::false])).
Definition reference_event_tail_7589 := match straight_drop 8059 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma reference_event_position_7589 : straight_drop 8058 flat_statements = Some (@Qcons VarOrder.T (@Snode VarOrder.T 7589 reference_event_expr_7589) reference_event_tail_7589).
Proof. vm_compute. reflexivity. Qed.
Lemma reference_event_suffix_7589 : memory_suffix_safe flat_memories 7589 reference_event_tail_7589.
Proof. apply memory_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma reference_event_nonregister_7589 : has_register 7589 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem reference_event_equation_7589 invalid old current result :
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 7589 result = eval_hfexpr_with_memory flat_memories reference_event_expr_7589 old old.
Proof.
 intro Step. exact (formal_combinational_node_equation _ _ _ _ _ invalid flat_memories old current result
 reference_event_position_7589 reference_event_suffix_7589 reference_event_nonregister_7589 Step).
Qed.
Print Assumptions reference_event_equation_7589.
