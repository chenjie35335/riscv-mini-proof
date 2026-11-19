Require Import CoreSocModel ComparisonNodes RegisterInvariants ScalarNodeFrames FormalTypedNodeFrames FormalTypedNodeEquation FormalSuccessfulNodeEvaluation.
From Coq Require Import ZArith.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From firrtl Require Import Firrtl_with_implicit_widths Env_with_implicit_widths HiEnv_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Definition reference_pc_sequential_6804_expr := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 6780)) (@Eref VarOrder.T (@Eid VarOrder.T 6803)) (@Eref VarOrder.T (@Eid VarOrder.T 6507))).
Definition reference_pc_sequential_6804_tail := match straight_drop 6884 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma reference_pc_sequential_6804_position : straight_drop 6883 flat_statements = Some (@Qcons VarOrder.T (@Snode VarOrder.T 6804 reference_pc_sequential_6804_expr) reference_pc_sequential_6804_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma reference_pc_sequential_6804_safe : formal_typed_suffix_safe flat_memories 6804 reference_pc_sequential_6804_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma reference_pc_sequential_6804_nonregister : has_register 6804 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem reference_pc_sequential_6804_value invalid old current result width bits :
 eval_hfexpr_with_memory flat_memories reference_pc_sequential_6804_expr old old = Some (Gval (Fuint width) bits) ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 6804 result = Some (Gval (Fuint width) bits).
Proof.
 intros Eval Step. eapply formal_combinational_known_node;
 [exact reference_pc_sequential_6804_position|exact reference_pc_sequential_6804_safe|exact reference_pc_sequential_6804_nonregister|exact Eval|reflexivity|exact Step].
Qed.
Theorem reference_pc_sequential_6804_evaluation invalid old current result :
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 exists value, eval_hfexpr_with_memory flat_memories reference_pc_sequential_6804_expr old old = Some value.
Proof.
 intro Step.
 exact (formal_successful_node_evaluation 6883 flat_statements reference_pc_sequential_6804_tail 6804 reference_pc_sequential_6804_expr invalid flat_memories old false current result reference_pc_sequential_6804_position Step).
Qed.
Definition reference_pc_sequential_6805_expr := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 1707)) (@Eref VarOrder.T (@Eid VarOrder.T 6804)) (@Econst VarOrder.T (Fuint 1) [::false])).
Definition reference_pc_sequential_6805_tail := match straight_drop 6885 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma reference_pc_sequential_6805_position : straight_drop 6884 flat_statements = Some (@Qcons VarOrder.T (@Snode VarOrder.T 6805 reference_pc_sequential_6805_expr) reference_pc_sequential_6805_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma reference_pc_sequential_6805_safe : formal_typed_suffix_safe flat_memories 6805 reference_pc_sequential_6805_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma reference_pc_sequential_6805_nonregister : has_register 6805 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem reference_pc_sequential_6805_value invalid old current result width bits :
 eval_hfexpr_with_memory flat_memories reference_pc_sequential_6805_expr old old = Some (Gval (Fuint width) bits) ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 6805 result = Some (Gval (Fuint width) bits).
Proof.
 intros Eval Step. eapply formal_combinational_known_node;
 [exact reference_pc_sequential_6805_position|exact reference_pc_sequential_6805_safe|exact reference_pc_sequential_6805_nonregister|exact Eval|reflexivity|exact Step].
Qed.
Theorem reference_pc_sequential_6805_evaluation invalid old current result :
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 exists value, eval_hfexpr_with_memory flat_memories reference_pc_sequential_6805_expr old old = Some value.
Proof.
 intro Step.
 exact (formal_successful_node_evaluation 6884 flat_statements reference_pc_sequential_6805_tail 6805 reference_pc_sequential_6805_expr invalid flat_memories old false current result reference_pc_sequential_6805_position Step).
Qed.
Definition reference_pc_sequential_6806_expr := (@Eref VarOrder.T (@Eid VarOrder.T 6805)).
Definition reference_pc_sequential_6806_tail := match straight_drop 6886 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma reference_pc_sequential_6806_position : straight_drop 6885 flat_statements = Some (@Qcons VarOrder.T (@Snode VarOrder.T 6806 reference_pc_sequential_6806_expr) reference_pc_sequential_6806_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma reference_pc_sequential_6806_safe : formal_typed_suffix_safe flat_memories 6806 reference_pc_sequential_6806_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma reference_pc_sequential_6806_nonregister : has_register 6806 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem reference_pc_sequential_6806_value invalid old current result width bits :
 eval_hfexpr_with_memory flat_memories reference_pc_sequential_6806_expr old old = Some (Gval (Fuint width) bits) ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 6806 result = Some (Gval (Fuint width) bits).
Proof.
 intros Eval Step. eapply formal_combinational_known_node;
 [exact reference_pc_sequential_6806_position|exact reference_pc_sequential_6806_safe|exact reference_pc_sequential_6806_nonregister|exact Eval|reflexivity|exact Step].
Qed.
Theorem reference_pc_sequential_6806_evaluation invalid old current result :
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 exists value, eval_hfexpr_with_memory flat_memories reference_pc_sequential_6806_expr old old = Some value.
Proof.
 intro Step.
 exact (formal_successful_node_evaluation 6885 flat_statements reference_pc_sequential_6806_tail 6806 reference_pc_sequential_6806_expr invalid flat_memories old false current result reference_pc_sequential_6806_position Step).
Qed.
Definition reference_pc_sequential_6807_expr := (@Eprim_binop VarOrder.T (Bcomp Beq) (@Eref VarOrder.T (@Eid VarOrder.T 6806)) (@Econst VarOrder.T (Fuint 1) [::false])).
Definition reference_pc_sequential_6807_tail := match straight_drop 6887 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma reference_pc_sequential_6807_position : straight_drop 6886 flat_statements = Some (@Qcons VarOrder.T (@Snode VarOrder.T 6807 reference_pc_sequential_6807_expr) reference_pc_sequential_6807_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma reference_pc_sequential_6807_safe : formal_typed_suffix_safe flat_memories 6807 reference_pc_sequential_6807_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma reference_pc_sequential_6807_nonregister : has_register 6807 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem reference_pc_sequential_6807_value invalid old current result width bits :
 eval_hfexpr_with_memory flat_memories reference_pc_sequential_6807_expr old old = Some (Gval (Fuint width) bits) ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 6807 result = Some (Gval (Fuint width) bits).
Proof.
 intros Eval Step. eapply formal_combinational_known_node;
 [exact reference_pc_sequential_6807_position|exact reference_pc_sequential_6807_safe|exact reference_pc_sequential_6807_nonregister|exact Eval|reflexivity|exact Step].
Qed.
Theorem reference_pc_sequential_6807_evaluation invalid old current result :
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 exists value, eval_hfexpr_with_memory flat_memories reference_pc_sequential_6807_expr old old = Some value.
Proof.
 intro Step.
 exact (formal_successful_node_evaluation 6886 flat_statements reference_pc_sequential_6807_tail 6807 reference_pc_sequential_6807_expr invalid flat_memories old false current result reference_pc_sequential_6807_position Step).
Qed.
Definition reference_pc_sequential_6808_expr := (@Eprim_binop VarOrder.T Badd (@Eref VarOrder.T (@Eid VarOrder.T 2812)) (@Econst VarOrder.T (Fuint 3) [::false; false; true])).
Definition reference_pc_sequential_6808_tail := match straight_drop 6888 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma reference_pc_sequential_6808_position : straight_drop 6887 flat_statements = Some (@Qcons VarOrder.T (@Snode VarOrder.T 6808 reference_pc_sequential_6808_expr) reference_pc_sequential_6808_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma reference_pc_sequential_6808_safe : formal_typed_suffix_safe flat_memories 6808 reference_pc_sequential_6808_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma reference_pc_sequential_6808_nonregister : has_register 6808 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem reference_pc_sequential_6808_value invalid old current result width bits :
 eval_hfexpr_with_memory flat_memories reference_pc_sequential_6808_expr old old = Some (Gval (Fuint width) bits) ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 6808 result = Some (Gval (Fuint width) bits).
Proof.
 intros Eval Step. eapply formal_combinational_known_node;
 [exact reference_pc_sequential_6808_position|exact reference_pc_sequential_6808_safe|exact reference_pc_sequential_6808_nonregister|exact Eval|reflexivity|exact Step].
Qed.
Theorem reference_pc_sequential_6808_evaluation invalid old current result :
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 exists value, eval_hfexpr_with_memory flat_memories reference_pc_sequential_6808_expr old old = Some value.
Proof.
 intro Step.
 exact (formal_successful_node_evaluation 6887 flat_statements reference_pc_sequential_6808_tail 6808 reference_pc_sequential_6808_expr invalid flat_memories old false current result reference_pc_sequential_6808_position Step).
Qed.
Definition reference_pc_sequential_6809_expr := (@Eprim_unop VarOrder.T (Utail 1) (@Eref VarOrder.T (@Eid VarOrder.T 6808))).
Definition reference_pc_sequential_6809_tail := match straight_drop 6889 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma reference_pc_sequential_6809_position : straight_drop 6888 flat_statements = Some (@Qcons VarOrder.T (@Snode VarOrder.T 6809 reference_pc_sequential_6809_expr) reference_pc_sequential_6809_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma reference_pc_sequential_6809_safe : formal_typed_suffix_safe flat_memories 6809 reference_pc_sequential_6809_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma reference_pc_sequential_6809_nonregister : has_register 6809 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem reference_pc_sequential_6809_value invalid old current result width bits :
 eval_hfexpr_with_memory flat_memories reference_pc_sequential_6809_expr old old = Some (Gval (Fuint width) bits) ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 6809 result = Some (Gval (Fuint width) bits).
Proof.
 intros Eval Step. eapply formal_combinational_known_node;
 [exact reference_pc_sequential_6809_position|exact reference_pc_sequential_6809_safe|exact reference_pc_sequential_6809_nonregister|exact Eval|reflexivity|exact Step].
Qed.
Theorem reference_pc_sequential_6809_evaluation invalid old current result :
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 exists value, eval_hfexpr_with_memory flat_memories reference_pc_sequential_6809_expr old old = Some value.
Proof.
 intro Step.
 exact (formal_successful_node_evaluation 6888 flat_statements reference_pc_sequential_6809_tail 6809 reference_pc_sequential_6809_expr invalid flat_memories old false current result reference_pc_sequential_6809_position Step).
Qed.
Definition reference_pc_sequential_6810_expr := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 6807)) (@Eref VarOrder.T (@Eid VarOrder.T 6809)) (@Eref VarOrder.T (@Eid VarOrder.T 6508))).
Definition reference_pc_sequential_6810_tail := match straight_drop 6890 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma reference_pc_sequential_6810_position : straight_drop 6889 flat_statements = Some (@Qcons VarOrder.T (@Snode VarOrder.T 6810 reference_pc_sequential_6810_expr) reference_pc_sequential_6810_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma reference_pc_sequential_6810_safe : formal_typed_suffix_safe flat_memories 6810 reference_pc_sequential_6810_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma reference_pc_sequential_6810_nonregister : has_register 6810 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem reference_pc_sequential_6810_value invalid old current result width bits :
 eval_hfexpr_with_memory flat_memories reference_pc_sequential_6810_expr old old = Some (Gval (Fuint width) bits) ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 6810 result = Some (Gval (Fuint width) bits).
Proof.
 intros Eval Step. eapply formal_combinational_known_node;
 [exact reference_pc_sequential_6810_position|exact reference_pc_sequential_6810_safe|exact reference_pc_sequential_6810_nonregister|exact Eval|reflexivity|exact Step].
Qed.
Theorem reference_pc_sequential_6810_evaluation invalid old current result :
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 exists value, eval_hfexpr_with_memory flat_memories reference_pc_sequential_6810_expr old old = Some value.
Proof.
 intro Step.
 exact (formal_successful_node_evaluation 6889 flat_statements reference_pc_sequential_6810_tail 6810 reference_pc_sequential_6810_expr invalid flat_memories old false current result reference_pc_sequential_6810_position Step).
Qed.
Definition reference_pc_sequential_7094_expr := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 6780)) (@Eref VarOrder.T (@Eid VarOrder.T 7060)) (@Eref VarOrder.T (@Eid VarOrder.T 6810))).
Definition reference_pc_sequential_7094_tail := match straight_drop 7174 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma reference_pc_sequential_7094_position : straight_drop 7173 flat_statements = Some (@Qcons VarOrder.T (@Snode VarOrder.T 7094 reference_pc_sequential_7094_expr) reference_pc_sequential_7094_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma reference_pc_sequential_7094_safe : formal_typed_suffix_safe flat_memories 7094 reference_pc_sequential_7094_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma reference_pc_sequential_7094_nonregister : has_register 7094 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem reference_pc_sequential_7094_value invalid old current result width bits :
 eval_hfexpr_with_memory flat_memories reference_pc_sequential_7094_expr old old = Some (Gval (Fuint width) bits) ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 7094 result = Some (Gval (Fuint width) bits).
Proof.
 intros Eval Step. eapply formal_combinational_known_node;
 [exact reference_pc_sequential_7094_position|exact reference_pc_sequential_7094_safe|exact reference_pc_sequential_7094_nonregister|exact Eval|reflexivity|exact Step].
Qed.
Theorem reference_pc_sequential_7094_evaluation invalid old current result :
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 exists value, eval_hfexpr_with_memory flat_memories reference_pc_sequential_7094_expr old old = Some value.
Proof.
 intro Step.
 exact (formal_successful_node_evaluation 7173 flat_statements reference_pc_sequential_7094_tail 7094 reference_pc_sequential_7094_expr invalid flat_memories old false current result reference_pc_sequential_7094_position Step).
Qed.
Print Assumptions reference_pc_sequential_7094_value.
