Require Import CoreSocModel ComparisonNodes RegisterInvariants ScalarNodeFrames FormalTypedNodeFrames FormalTypedNodeEquation FormalSuccessfulNodeEvaluation.
From Coq Require Import ZArith.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From firrtl Require Import Firrtl_with_implicit_widths Env_with_implicit_widths HiEnv_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Definition fetch_pc_reset_7766_expr := (@Eprim_binop VarOrder.T Bsub (@Econst VarOrder.T (Fuint 32) [::false; false; false; false; false; false; false; false; false; true; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false]) (@Econst VarOrder.T (Fuint 32) [::false; false; true; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false])).
Definition fetch_pc_reset_7766_tail := match straight_drop 8273 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma fetch_pc_reset_7766_position : straight_drop 8272 flat_statements = Some (@Qcons VarOrder.T (@Snode VarOrder.T 7766 fetch_pc_reset_7766_expr) fetch_pc_reset_7766_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma fetch_pc_reset_7766_safe : formal_typed_suffix_safe flat_memories 7766 fetch_pc_reset_7766_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma fetch_pc_reset_7766_nonregister : has_register 7766 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem fetch_pc_reset_7766_value invalid old current result width bits :
 eval_hfexpr_with_memory flat_memories fetch_pc_reset_7766_expr old old = Some (Gval (Fuint width) bits) ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 7766 result = Some (Gval (Fuint width) bits).
Proof.
 intros Eval Step. eapply formal_combinational_known_node;
 [exact fetch_pc_reset_7766_position|exact fetch_pc_reset_7766_safe|exact fetch_pc_reset_7766_nonregister|exact Eval|reflexivity|exact Step].
Qed.
Theorem fetch_pc_reset_7766_evaluation invalid old current result :
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 exists value, eval_hfexpr_with_memory flat_memories fetch_pc_reset_7766_expr old old = Some value.
Proof.
 intro Step.
 exact (formal_successful_node_evaluation 8272 flat_statements fetch_pc_reset_7766_tail 7766 fetch_pc_reset_7766_expr invalid flat_memories old false current result fetch_pc_reset_7766_position Step).
Qed.
Definition fetch_pc_reset_7767_expr := (@Eprim_unop VarOrder.T (Utail 1) (@Eref VarOrder.T (@Eid VarOrder.T 7766))).
Definition fetch_pc_reset_7767_tail := match straight_drop 8274 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma fetch_pc_reset_7767_position : straight_drop 8273 flat_statements = Some (@Qcons VarOrder.T (@Snode VarOrder.T 7767 fetch_pc_reset_7767_expr) fetch_pc_reset_7767_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma fetch_pc_reset_7767_safe : formal_typed_suffix_safe flat_memories 7767 fetch_pc_reset_7767_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma fetch_pc_reset_7767_nonregister : has_register 7767 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem fetch_pc_reset_7767_value invalid old current result width bits :
 eval_hfexpr_with_memory flat_memories fetch_pc_reset_7767_expr old old = Some (Gval (Fuint width) bits) ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 7767 result = Some (Gval (Fuint width) bits).
Proof.
 intros Eval Step. eapply formal_combinational_known_node;
 [exact fetch_pc_reset_7767_position|exact fetch_pc_reset_7767_safe|exact fetch_pc_reset_7767_nonregister|exact Eval|reflexivity|exact Step].
Qed.
Theorem fetch_pc_reset_7767_evaluation invalid old current result :
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 exists value, eval_hfexpr_with_memory flat_memories fetch_pc_reset_7767_expr old old = Some value.
Proof.
 intro Step.
 exact (formal_successful_node_evaluation 8273 flat_statements fetch_pc_reset_7767_tail 7767 fetch_pc_reset_7767_expr invalid flat_memories old false current result fetch_pc_reset_7767_position Step).
Qed.
Print Assumptions fetch_pc_reset_7767_value.
