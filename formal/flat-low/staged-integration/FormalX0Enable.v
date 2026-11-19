Require Import CoreSocModel ComparisonNodes FormalNodeEquation MemorySuffixCertificates MemoryWriteFrames ScalarNodeFrames RegisterInvariants.
From Coq Require Import ZArith.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths Firrtl_with_implicit_widths HiEnv_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Require Import FormalCheckerValidOutput FormalDeclaredConnectionObservation FormalSuccessfulNode FormalComparisonBitShape NormalizedBit.
Definition checker_valid_expr_7601 := (@Eprim_binop VarOrder.T (Bcomp Beq) (@Eref VarOrder.T (@Eid VarOrder.T 7600)) (@Econst VarOrder.T (Fuint 1) [::false])).
Definition checker_valid_tail_7601 := match straight_drop 8071 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma checker_valid_position_7601 : straight_drop 8070 flat_statements = Some (@Qcons VarOrder.T (@Snode VarOrder.T 7601 checker_valid_expr_7601) checker_valid_tail_7601).
Proof. vm_compute. reflexivity. Qed.
Lemma checker_valid_suffix_7601 : memory_suffix_safe flat_memories 7601 checker_valid_tail_7601.
Proof. apply memory_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma checker_valid_nonregister_7601 : has_register 7601 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem checker_valid_equation_7601 invalid old current result :
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 7601 result = eval_hfexpr_with_memory flat_memories checker_valid_expr_7601 old old.
Proof.
 intro Step. exact (formal_combinational_node_equation _ _ _ _ _ invalid flat_memories old current result
 checker_valid_position_7601 checker_valid_suffix_7601 checker_valid_nonregister_7601 Step).
Qed.
Theorem x0_guard_normalized invalid old current result :
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 exists value, VM.find 7601 result = Some value /\ normalized_bit value.
Proof.
 intro Step.
 destruct (formal_successful_node _ _ _ _ _ invalid flat_memories old false current result checker_valid_position_7601 Step) as [value Eval].
 change (eval_hfexpr_with_memory flat_memories checker_valid_expr_7601 old old = Some value) in Eval.
 exists value. split.
 - rewrite (checker_valid_equation_7601 invalid old current result Step). exact Eval.
 - cbn [checker_valid_expr_7601 eval_hfexpr_with_memory eval_href_with_memory] in Eval.
   destruct (VM.find 7600 old) as [source|]; [|discriminate Eval].
   exact (comparison_false_normalized source value Eval).
Qed.
Theorem checker_output_normalized invalid old current result :
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 exists value, VM.find 1395 result = Some value /\ normalized_bit value.
Proof.
 intro Step.
 destruct (declared_connection_observation 1474 flat_statements checker_output_decl_1395 checker_output_mid_1395 checker_output_tail_1395
 1395 7956 1 invalid flat_memories old current result
 checker_output_position_1395 checker_output_split_1395 checker_output_straight_1395 checker_output_mid_safe_1395 checker_output_tail_safe_1395
 checker_output_nonregister_1395 (Logic.eq_refl _) Step) as [source [value [Source [Adapt Value]]]].
 exists value. split; [exact Value|exact (adapted_bit_normalized source value Adapt)].
Qed.
Definition x0_enable := (@Eprim_binop VarOrder.T Band (@Eprim_binop VarOrder.T Band
 (@Eprim_binop VarOrder.T Band (@Econst VarOrder.T (Fuint 1) [::true])
 (@Eref VarOrder.T (@Eid VarOrder.T 1395)))
 (@Eref VarOrder.T (@Eid VarOrder.T 7601))) (@Econst VarOrder.T (Fuint 1) [::true])).
Lemma x0_enabled_normalized sem value guard :
 VM.find 1395 sem = Some value -> normalized_bit value ->
 VM.find 7601 sem = Some guard -> normalized_bit guard ->
 generated_expr_true x0_enable sem -> value = Gval (Fuint 1) [::true].
Proof.
 intros Valid Normal Guard GuardNormal Enabled.
 unfold generated_expr_true, x0_enable in Enabled.
 cbn [eval_hfexpr eval_href] in Enabled. rewrite Valid Guard in Enabled.
 destruct Normal as [b| | |]; destruct GuardNormal as [g| | |];
 try destruct b; try destruct g; vm_compute in Enabled;
 try discriminate Enabled; try contradiction; reflexivity.
Qed.
Theorem formal_x0_enable_valid invalid old current result :
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 generated_expr_true x0_enable result ->
 VM.find 1395 result = Some (Gval (Fuint 1) [::true]).
Proof.
 intros Step Enabled.
 destruct (checker_output_normalized invalid old current result Step) as [value [Value Normal]].
 destruct (x0_guard_normalized invalid old current result Step) as [guard [Guard GuardNormal]].
 pose proof (x0_enabled_normalized result value guard Value Normal Guard GuardNormal Enabled) as Equal.
 rewrite Equal in Value. exact Value.
Qed.
Print Assumptions formal_x0_enable_valid.
