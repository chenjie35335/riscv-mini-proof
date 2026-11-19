Require Import CoreSocModel ComparisonNodes FormalNodeEquation FormalTypedNodeEquation FormalTypedNodeFrames MemorySuffixCertificates MemoryWriteFrames ScalarNodeFrames RegisterInvariants.
From Coq Require Import ZArith.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths Firrtl_with_implicit_widths HiEnv_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Definition reference_event_expr_7741 := (@Ecast VarOrder.T AsUInt (@Eref VarOrder.T (@Eid VarOrder.T 1394))).
Definition reference_event_tail_7741 := match straight_drop 8199 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma reference_event_position_7741 : straight_drop 8198 flat_statements = Some (@Qcons VarOrder.T (@Snode VarOrder.T 7729 reference_event_expr_7741) reference_event_tail_7741).
Proof. vm_compute. reflexivity. Qed.
Lemma reference_event_suffix_7741 : memory_suffix_safe flat_memories 7729 reference_event_tail_7741.
Proof. apply memory_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma reference_event_nonregister_7741 : has_register 7729 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem reference_event_equation_7741 invalid old current result :
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 7729 result = eval_hfexpr_with_memory flat_memories reference_event_expr_7741 old old.
Proof.
 intro Step. exact (formal_combinational_node_equation _ _ _ _ _ invalid flat_memories old current result
 reference_event_position_7741 reference_event_suffix_7741 reference_event_nonregister_7741 Step).
Qed.
Definition reference_event_expr_7742 := (@Eprim_binop VarOrder.T (Bcomp Beq) (@Eref VarOrder.T (@Eid VarOrder.T 7729)) (@Econst VarOrder.T (Fuint 1) [::false])).
Definition reference_event_tail_7742 := match straight_drop 8200 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma reference_event_position_7742 : straight_drop 8199 flat_statements = Some (@Qcons VarOrder.T (@Snode VarOrder.T 7730 reference_event_expr_7742) reference_event_tail_7742).
Proof. vm_compute. reflexivity. Qed.
Lemma reference_event_suffix_7742 : memory_suffix_safe flat_memories 7730 reference_event_tail_7742.
Proof. apply memory_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma reference_event_nonregister_7742 : has_register 7730 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem reference_event_equation_7742 invalid old current result :
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 7730 result = eval_hfexpr_with_memory flat_memories reference_event_expr_7742 old old.
Proof.
 intro Step. exact (formal_combinational_node_equation _ _ _ _ _ invalid flat_memories old current result
 reference_event_position_7742 reference_event_suffix_7742 reference_event_nonregister_7742 Step).
Qed.
