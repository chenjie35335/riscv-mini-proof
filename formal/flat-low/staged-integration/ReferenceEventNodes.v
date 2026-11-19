Require Import CoreSocModel ComparisonNodes FormalNodeEquation FormalTypedNodeEquation FormalTypedNodeFrames MemorySuffixCertificates MemoryWriteFrames ScalarNodeFrames RegisterInvariants.
From Coq Require Import ZArith.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths Firrtl_with_implicit_widths HiEnv_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Definition reference_event_expr_7083 := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 6780)) (@Econst VarOrder.T (Fuint 1) [::true]) (@Econst VarOrder.T (Fuint 1) [::false])).
Definition reference_event_tail_7083 := match straight_drop 7163 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma reference_event_position_7083 : straight_drop 7162 flat_statements = Some (@Qcons VarOrder.T (@Snode VarOrder.T 7083 reference_event_expr_7083) reference_event_tail_7083).
Proof. vm_compute. reflexivity. Qed.
Lemma reference_event_suffix_7083 : memory_suffix_safe flat_memories 7083 reference_event_tail_7083.
Proof. apply memory_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma reference_event_nonregister_7083 : has_register 7083 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem reference_event_equation_7083 invalid old current result :
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 7083 result = eval_hfexpr_with_memory flat_memories reference_event_expr_7083 old old.
Proof.
 intro Step. exact (formal_combinational_node_equation _ _ _ _ _ invalid flat_memories old current result
 reference_event_position_7083 reference_event_suffix_7083 reference_event_nonregister_7083 Step).
Qed.
Definition reference_event_expr_7116 := (@Econst VarOrder.T (Fuint 1) [::false]).
Definition reference_event_tail_7116 := match straight_drop 7196 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma reference_event_position_7116 : straight_drop 7195 flat_statements = Some (@Qcons VarOrder.T (@Snode VarOrder.T 7116 reference_event_expr_7116) reference_event_tail_7116).
Proof. vm_compute. reflexivity. Qed.
Lemma reference_event_suffix_7116 : memory_suffix_safe flat_memories 7116 reference_event_tail_7116.
Proof. apply memory_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma reference_event_nonregister_7116 : has_register 7116 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem reference_event_equation_7116 invalid old current result :
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 7116 result = eval_hfexpr_with_memory flat_memories reference_event_expr_7116 old old.
Proof.
 intro Step. exact (formal_combinational_node_equation _ _ _ _ _ invalid flat_memories old current result
 reference_event_position_7116 reference_event_suffix_7116 reference_event_nonregister_7116 Step).
Qed.
Definition reference_event_expr_7117 := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 1707)) (@Eref VarOrder.T (@Eid VarOrder.T 7083)) (@Eref VarOrder.T (@Eid VarOrder.T 7116))).
Definition reference_event_tail_7117 := match straight_drop 7197 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma reference_event_position_7117 : straight_drop 7196 flat_statements = Some (@Qcons VarOrder.T (@Snode VarOrder.T 7117 reference_event_expr_7117) reference_event_tail_7117).
Proof. vm_compute. reflexivity. Qed.
Lemma reference_event_suffix_7117 : memory_suffix_safe flat_memories 7117 reference_event_tail_7117.
Proof. apply memory_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma reference_event_nonregister_7117 : has_register 7117 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem reference_event_equation_7117 invalid old current result :
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 7117 result = eval_hfexpr_with_memory flat_memories reference_event_expr_7117 old old.
Proof.
 intro Step. exact (formal_combinational_node_equation _ _ _ _ _ invalid flat_memories old current result
 reference_event_position_7117 reference_event_suffix_7117 reference_event_nonregister_7117 Step).
Qed.
Definition reference_event_expr_7202 := (@Eref VarOrder.T (@Eid VarOrder.T 7117)).
Definition reference_event_tail_7202 := match straight_drop 7282 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma reference_event_position_7202 : straight_drop 7281 flat_statements = Some (@Qcons VarOrder.T (@Snode VarOrder.T 7202 reference_event_expr_7202) reference_event_tail_7202).
Proof. vm_compute. reflexivity. Qed.
Lemma reference_event_suffix_7202 : formal_typed_suffix_safe flat_memories 7202 reference_event_tail_7202.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma reference_event_nonregister_7202 : has_register 7202 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem reference_event_value_7202 invalid old current result value :
 eval_hfexpr_with_memory flat_memories reference_event_expr_7202 old old = Some value ->
 type_of_val value = Gtyp (Fuint 1) ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 7202 result = Some value.
Proof.
 intros Eval Typed Step. eapply formal_combinational_known_node;
 [exact reference_event_position_7202|exact reference_event_suffix_7202|exact reference_event_nonregister_7202|exact Eval|exact Typed|exact Step].
Qed.
Definition reference_event_expr_7727 := (@Eprim_binop VarOrder.T Bor (@Eref VarOrder.T (@Eid VarOrder.T 1469)) (@Eref VarOrder.T (@Eid VarOrder.T 1667))).
Definition reference_event_tail_7727 := match straight_drop 8197 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma reference_event_position_7727 : straight_drop 8196 flat_statements = Some (@Qcons VarOrder.T (@Snode VarOrder.T 7727 reference_event_expr_7727) reference_event_tail_7727).
Proof. vm_compute. reflexivity. Qed.
Lemma reference_event_suffix_7727 : memory_suffix_safe flat_memories 7727 reference_event_tail_7727.
Proof. apply memory_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma reference_event_nonregister_7727 : has_register 7727 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem reference_event_equation_7727 invalid old current result :
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 7727 result = eval_hfexpr_with_memory flat_memories reference_event_expr_7727 old old.
Proof.
 intro Step. exact (formal_combinational_node_equation _ _ _ _ _ invalid flat_memories old current result
 reference_event_position_7727 reference_event_suffix_7727 reference_event_nonregister_7727 Step).
Qed.
Definition reference_event_expr_7745 := (@Ecast VarOrder.T AsUInt (@Eref VarOrder.T (@Eid VarOrder.T 1394))).
Definition reference_event_tail_7745 := match straight_drop 8215 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma reference_event_position_7745 : straight_drop 8214 flat_statements = Some (@Qcons VarOrder.T (@Snode VarOrder.T 7745 reference_event_expr_7745) reference_event_tail_7745).
Proof. vm_compute. reflexivity. Qed.
Lemma reference_event_suffix_7745 : memory_suffix_safe flat_memories 7745 reference_event_tail_7745.
Proof. apply memory_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma reference_event_nonregister_7745 : has_register 7745 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem reference_event_equation_7745 invalid old current result :
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 7745 result = eval_hfexpr_with_memory flat_memories reference_event_expr_7745 old old.
Proof.
 intro Step. exact (formal_combinational_node_equation _ _ _ _ _ invalid flat_memories old current result
 reference_event_position_7745 reference_event_suffix_7745 reference_event_nonregister_7745 Step).
Qed.
Definition reference_event_expr_7746 := (@Eprim_binop VarOrder.T (Bcomp Beq) (@Eref VarOrder.T (@Eid VarOrder.T 7745)) (@Econst VarOrder.T (Fuint 1) [::false])).
Definition reference_event_tail_7746 := match straight_drop 8216 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma reference_event_position_7746 : straight_drop 8215 flat_statements = Some (@Qcons VarOrder.T (@Snode VarOrder.T 7746 reference_event_expr_7746) reference_event_tail_7746).
Proof. vm_compute. reflexivity. Qed.
Lemma reference_event_suffix_7746 : memory_suffix_safe flat_memories 7746 reference_event_tail_7746.
Proof. apply memory_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma reference_event_nonregister_7746 : has_register 7746 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem reference_event_equation_7746 invalid old current result :
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 7746 result = eval_hfexpr_with_memory flat_memories reference_event_expr_7746 old old.
Proof.
 intro Step. exact (formal_combinational_node_equation _ _ _ _ _ invalid flat_memories old current result
 reference_event_position_7746 reference_event_suffix_7746 reference_event_nonregister_7746 Step).
Qed.
Print Assumptions reference_event_equation_7746.
