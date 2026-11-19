Require Import SelectedNodeSafety JointUpdateNodePositions JointUpdateExpressionCertificates JointUpdateConnectionCertificates CoreSocModel ComparisonNodes ScalarNodeFrames FormalTypedNodeFrames RegisterInvariants FormalTypedNodeEquation FormalDeclaredConnection FormalStatementSegments RegisterCommitCertificate FormalUIntRegisterCommitSource SelectedUIntMuxIdentity UIntResizeRoundtrip.
From Coq Require Import ZArith List Lia.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From nbits Require Import NBits.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Definition rfa_reset_word_28 inputs path := proj1_sig (formal_symbolic_inputs inputs path (validif_source_address (validif_raw_address nil 8651 0 nil)) nil 32).
Lemma rfa_reset_word_28_size inputs path : size (rfa_reset_word_28 inputs path) = 32%nat.
Proof. exact (proj2_sig (formal_symbolic_inputs inputs path (validif_source_address (validif_raw_address nil 8651 0 nil)) nil 32)). Qed.
Definition rfa_node_8145_expr := (@Evalidif VarOrder.T (@Econst VarOrder.T (Fuint 1) [::false]) (@Econst VarOrder.T (Fuint 32) [::false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false])).
Definition rfa_node_8145_tail := match straight_drop 8652 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma rfa_node_8145_position : straight_drop 8651 flat_statements = Some (@Qcons VarOrder.T (@Snode VarOrder.T 8145 rfa_node_8145_expr) rfa_node_8145_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma rfa_node_8145_safe : formal_typed_suffix_safe flat_memories 8145 rfa_node_8145_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma rfa_node_8145_nonreg : has_register 8145 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem rfa_reset_step_8145 inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 VM.find 8145 result = Some (Gval (Fuint 32) (rfa_reset_word_28 inputs path)).
Proof.
 intros Step.
 eapply formal_combinational_known_node;
 [exact rfa_node_8145_position|exact rfa_node_8145_safe|exact rfa_node_8145_nonreg| |reflexivity|exact Step].
 reflexivity.
Qed.
Theorem rfa_reset_history_8145 inputs path history limit :
 (forall t, (t < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history t) false (history t) flat_statements = Some (history (S t))) ->
 forall t, (1 <= t)%coq_nat -> (t <= limit)%coq_nat ->
 VM.find 8145 (history t) = Some (Gval (Fuint 32) (rfa_reset_word_28 inputs path)).
Proof.
 intros Steps t Lower Upper. destruct t as [|t]; [lia|].
 apply (rfa_reset_step_8145 inputs path (history t) (history t) (history (S t))).
 apply Steps;lia.
Qed.
Definition rfa_node_8146_expr := joint_update_expr_8146.
Theorem rfa_reset_step_8146 inputs path old current result :
 VM.find 8145 old = Some (Gval (Fuint 32) (rfa_reset_word_28 inputs path)) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 VM.find 8146 result = Some (Gval (Fuint 32) (rfa_reset_word_28 inputs path)).
Proof.
 intros Source Step.
 assert (Member : List.In (8146,joint_update_expr_8146) joint_update_expected_nodes).
 { apply (List.nth_error_In joint_update_expected_nodes 1033%nat). vm_compute. reflexivity. }
 destruct (selected_node_safe_position flat_memories flat_statements joint_update_node_offsets flat_statements joint_update_expected_nodes 8146 joint_update_expr_8146 joint_update_node_positions joint_update_node_safety Member) as [count [tail [Position [Safe Nonreg]]]].
 eapply formal_combinational_known_node; [exact Position|exact Safe|exact Nonreg| |reflexivity|exact Step].
 cbn [rfa_node_8146_expr eval_hfexpr_validif_policy eval_href_validif_policy]. exact Source.
Qed.
Theorem rfa_reset_history_8146 inputs path history limit :
 (forall t, (t < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history t) false (history t) flat_statements = Some (history (S t))) ->
 forall t, (2 <= t)%coq_nat -> (t <= limit)%coq_nat ->
 VM.find 8146 (history t) = Some (Gval (Fuint 32) (rfa_reset_word_28 inputs path)).
Proof.
 intros Steps t Lower Upper. destruct t as [|t]; [lia|].
 apply (rfa_reset_step_8146 inputs path (history t) (history t) (history (S t))).
 - apply (rfa_reset_history_8145 inputs path history limit Steps t);lia.
 - apply Steps;lia.
Qed.
Lemma joint_update_connection_815_nonreg : has_register 815 flat_statements = false.
Proof. exact joint_update_connection_815_nonregister. Qed.
Theorem rfa_reset_step_815 inputs path old current result :
 VM.find 8146 old = Some (Gval (Fuint 32) (rfa_reset_word_28 inputs path)) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 VM.find 815 result = Some (Gval (Fuint 32) (rfa_reset_word_28 inputs path)).
Proof.
 intros Source Step.
 apply (declared_connection_value 824 flat_statements joint_update_connection_815_decl joint_update_connection_815_mid joint_update_connection_815_tail 815 8146 32
 (Gval (Fuint 32) (rfa_reset_word_28 inputs path)) (Gval (Fuint 32) (rfa_reset_word_28 inputs path))
 (formal_invalid_policy inputs path) flat_memories old current result joint_update_connection_815_position joint_update_connection_815_split joint_update_connection_815_straight joint_update_connection_815_mid_safe joint_update_connection_815_tail_safe joint_update_connection_815_nonreg (Logic.eq_refl _) Source).
 - assert (Take : take 32 (rfa_reset_word_28 inputs path) = rfa_reset_word_28 inputs path).
   { apply take_oversize. rewrite rfa_reset_word_28_size. reflexivity. }
   cbn [adapt_hvalue_as_type]. rewrite Take. unfold zext_to,zext. rewrite rfa_reset_word_28_size subnn cats0. reflexivity.
 - exact Step.
Qed.
Theorem rfa_reset_history_815 inputs path history limit :
 (forall t, (t < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history t) false (history t) flat_statements = Some (history (S t))) ->
 forall t, (3 <= t)%coq_nat -> (t <= limit)%coq_nat ->
 VM.find 815 (history t) = Some (Gval (Fuint 32) (rfa_reset_word_28 inputs path)).
Proof.
 intros Steps t Lower Upper. destruct t as [|t]; [lia|].
 apply (rfa_reset_step_815 inputs path (history t) (history t) (history (S t))).
 - apply (rfa_reset_history_8146 inputs path history limit Steps t);lia.
 - apply Steps;lia.
Qed.
Definition rfa_node_1113_expr := joint_update_expr_1113.
Theorem rfa_reset_step_1113 inputs path old current result :
 VM.find 815 old = Some (Gval (Fuint 32) (rfa_reset_word_28 inputs path)) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 VM.find 1113 result = Some (Gval (Fuint 32) (rfa_reset_word_28 inputs path)).
Proof.
 intros Source Step.
 assert (Member : List.In (1113,joint_update_expr_1113) joint_update_expected_nodes).
 { apply (List.nth_error_In joint_update_expected_nodes 703%nat). vm_compute. reflexivity. }
 destruct (selected_node_safe_position flat_memories flat_statements joint_update_node_offsets flat_statements joint_update_expected_nodes 1113 joint_update_expr_1113 joint_update_node_positions joint_update_node_safety Member) as [count [tail [Position [Safe Nonreg]]]].
 eapply formal_combinational_known_node; [exact Position|exact Safe|exact Nonreg| |reflexivity|exact Step].
 cbn [rfa_node_1113_expr eval_hfexpr_validif_policy eval_href_validif_policy]. exact Source.
Qed.
Theorem rfa_reset_history_1113 inputs path history limit :
 (forall t, (t < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history t) false (history t) flat_statements = Some (history (S t))) ->
 forall t, (4 <= t)%coq_nat -> (t <= limit)%coq_nat ->
 VM.find 1113 (history t) = Some (Gval (Fuint 32) (rfa_reset_word_28 inputs path)).
Proof.
 intros Steps t Lower Upper. destruct t as [|t]; [lia|].
 apply (rfa_reset_step_1113 inputs path (history t) (history t) (history (S t))).
 - apply (rfa_reset_history_815 inputs path history limit Steps t);lia.
 - apply Steps;lia.
Qed.
Definition rfa_wire_1510_decl := match straight_drop 1590 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition rfa_wire_1510_tail := match straight_drop 8999 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition rfa_wire_1510_mid := take_statements 7408 rfa_wire_1510_decl.
Lemma rfa_wire_1510_position : straight_drop 1589 flat_statements = Some (@Qcons VarOrder.T (@Swire VarOrder.T 1510 (Gtyp (Fuint 32))) rfa_wire_1510_decl).
Proof. vm_compute. reflexivity. Qed.
Lemma rfa_wire_1510_split : rfa_wire_1510_decl = statement_append rfa_wire_1510_mid (@Qcons VarOrder.T (@Sfcnct VarOrder.T (@Eid VarOrder.T 1510) (@Eref VarOrder.T (@Eid VarOrder.T 8146))) rfa_wire_1510_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma rfa_wire_1510_straight : straight_statements rfa_wire_1510_mid.
Proof. vm_compute. exact I. Qed.
Lemma rfa_wire_1510_mid_safe : formal_typed_suffix_safe flat_memories 1510 rfa_wire_1510_mid.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma rfa_wire_1510_tail_safe : formal_typed_suffix_safe flat_memories 1510 rfa_wire_1510_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma rfa_wire_1510_nonreg : has_register 1510 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem rfa_reset_step_1510 inputs path old current result :
 VM.find 8146 old = Some (Gval (Fuint 32) (rfa_reset_word_28 inputs path)) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 VM.find 1510 result = Some (Gval (Fuint 32) (rfa_reset_word_28 inputs path)).
Proof.
 intros Source Step.
 apply (declared_connection_value 1589 flat_statements rfa_wire_1510_decl rfa_wire_1510_mid rfa_wire_1510_tail 1510 8146 32
 (Gval (Fuint 32) (rfa_reset_word_28 inputs path)) (Gval (Fuint 32) (rfa_reset_word_28 inputs path))
 (formal_invalid_policy inputs path) flat_memories old current result rfa_wire_1510_position rfa_wire_1510_split rfa_wire_1510_straight rfa_wire_1510_mid_safe rfa_wire_1510_tail_safe rfa_wire_1510_nonreg (Logic.eq_refl _) Source).
 - assert (Take : take 32 (rfa_reset_word_28 inputs path) = rfa_reset_word_28 inputs path).
   { apply take_oversize. rewrite rfa_reset_word_28_size. reflexivity. }
   cbn [adapt_hvalue_as_type]. rewrite Take. unfold zext_to,zext. rewrite rfa_reset_word_28_size subnn cats0. reflexivity.
 - exact Step.
Qed.
Theorem rfa_reset_history_1510 inputs path history limit :
 (forall t, (t < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history t) false (history t) flat_statements = Some (history (S t))) ->
 forall t, (3 <= t)%coq_nat -> (t <= limit)%coq_nat ->
 VM.find 1510 (history t) = Some (Gval (Fuint 32) (rfa_reset_word_28 inputs path)).
Proof.
 intros Steps t Lower Upper. destruct t as [|t]; [lia|].
 apply (rfa_reset_step_1510 inputs path (history t) (history t) (history (S t))).
 - apply (rfa_reset_history_8146 inputs path history limit Steps t);lia.
 - apply Steps;lia.
Qed.
Definition rfa_wire_1700_decl := match straight_drop 1780 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition rfa_wire_1700_tail := match straight_drop 8251 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition rfa_wire_1700_mid := take_statements 6470 rfa_wire_1700_decl.
Lemma rfa_wire_1700_position : straight_drop 1779 flat_statements = Some (@Qcons VarOrder.T (@Swire VarOrder.T 1700 (Gtyp (Fuint 32))) rfa_wire_1700_decl).
Proof. vm_compute. reflexivity. Qed.
Lemma rfa_wire_1700_split : rfa_wire_1700_decl = statement_append rfa_wire_1700_mid (@Qcons VarOrder.T (@Sfcnct VarOrder.T (@Eid VarOrder.T 1700) (@Eref VarOrder.T (@Eid VarOrder.T 1510))) rfa_wire_1700_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma rfa_wire_1700_straight : straight_statements rfa_wire_1700_mid.
Proof. vm_compute. exact I. Qed.
Lemma rfa_wire_1700_mid_safe : formal_typed_suffix_safe flat_memories 1700 rfa_wire_1700_mid.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma rfa_wire_1700_tail_safe : formal_typed_suffix_safe flat_memories 1700 rfa_wire_1700_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma rfa_wire_1700_nonreg : has_register 1700 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem rfa_reset_step_1700 inputs path old current result :
 VM.find 1510 old = Some (Gval (Fuint 32) (rfa_reset_word_28 inputs path)) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 VM.find 1700 result = Some (Gval (Fuint 32) (rfa_reset_word_28 inputs path)).
Proof.
 intros Source Step.
 apply (declared_connection_value 1779 flat_statements rfa_wire_1700_decl rfa_wire_1700_mid rfa_wire_1700_tail 1700 1510 32
 (Gval (Fuint 32) (rfa_reset_word_28 inputs path)) (Gval (Fuint 32) (rfa_reset_word_28 inputs path))
 (formal_invalid_policy inputs path) flat_memories old current result rfa_wire_1700_position rfa_wire_1700_split rfa_wire_1700_straight rfa_wire_1700_mid_safe rfa_wire_1700_tail_safe rfa_wire_1700_nonreg (Logic.eq_refl _) Source).
 - assert (Take : take 32 (rfa_reset_word_28 inputs path) = rfa_reset_word_28 inputs path).
   { apply take_oversize. rewrite rfa_reset_word_28_size. reflexivity. }
   cbn [adapt_hvalue_as_type]. rewrite Take. unfold zext_to,zext. rewrite rfa_reset_word_28_size subnn cats0. reflexivity.
 - exact Step.
Qed.
Theorem rfa_reset_history_1700 inputs path history limit :
 (forall t, (t < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history t) false (history t) flat_statements = Some (history (S t))) ->
 forall t, (4 <= t)%coq_nat -> (t <= limit)%coq_nat ->
 VM.find 1700 (history t) = Some (Gval (Fuint 32) (rfa_reset_word_28 inputs path)).
Proof.
 intros Steps t Lower Upper. destruct t as [|t]; [lia|].
 apply (rfa_reset_step_1700 inputs path (history t) (history t) (history (S t))).
 - apply (rfa_reset_history_1510 inputs path history limit Steps t);lia.
 - apply Steps;lia.
Qed.
Definition rfa_node_7425_expr := (@Eref VarOrder.T (@Eid VarOrder.T 1700)).
Definition rfa_node_7425_tail := match straight_drop 7597 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma rfa_node_7425_position : straight_drop 7596 flat_statements = Some (@Qcons VarOrder.T (@Snode VarOrder.T 7425 rfa_node_7425_expr) rfa_node_7425_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma rfa_node_7425_safe : formal_typed_suffix_safe flat_memories 7425 rfa_node_7425_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma rfa_node_7425_nonreg : has_register 7425 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem rfa_reset_step_7425 inputs path old current result :
 VM.find 1700 old = Some (Gval (Fuint 32) (rfa_reset_word_28 inputs path)) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 VM.find 7425 result = Some (Gval (Fuint 32) (rfa_reset_word_28 inputs path)).
Proof.
 intros Source Step.
 eapply formal_combinational_known_node;
 [exact rfa_node_7425_position|exact rfa_node_7425_safe|exact rfa_node_7425_nonreg| |reflexivity|exact Step].
 cbn [rfa_node_7425_expr eval_hfexpr_validif_policy eval_href_validif_policy]. exact Source.
Qed.
Theorem rfa_reset_history_7425 inputs path history limit :
 (forall t, (t < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history t) false (history t) flat_statements = Some (history (S t))) ->
 forall t, (5 <= t)%coq_nat -> (t <= limit)%coq_nat ->
 VM.find 7425 (history t) = Some (Gval (Fuint 32) (rfa_reset_word_28 inputs path)).
Proof.
 intros Steps t Lower Upper. destruct t as [|t]; [lia|].
 apply (rfa_reset_step_7425 inputs path (history t) (history t) (history (S t))).
 - apply (rfa_reset_history_1700 inputs path history limit Steps t);lia.
 - apply Steps;lia.
Qed.
Definition rfa_node_7426_expr := (@Eref VarOrder.T (@Eid VarOrder.T 7425)).
Definition rfa_node_7426_tail := match straight_drop 7598 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma rfa_node_7426_position : straight_drop 7597 flat_statements = Some (@Qcons VarOrder.T (@Snode VarOrder.T 7426 rfa_node_7426_expr) rfa_node_7426_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma rfa_node_7426_safe : formal_typed_suffix_safe flat_memories 7426 rfa_node_7426_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma rfa_node_7426_nonreg : has_register 7426 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem rfa_reset_step_7426 inputs path old current result :
 VM.find 7425 old = Some (Gval (Fuint 32) (rfa_reset_word_28 inputs path)) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 VM.find 7426 result = Some (Gval (Fuint 32) (rfa_reset_word_28 inputs path)).
Proof.
 intros Source Step.
 eapply formal_combinational_known_node;
 [exact rfa_node_7426_position|exact rfa_node_7426_safe|exact rfa_node_7426_nonreg| |reflexivity|exact Step].
 cbn [rfa_node_7426_expr eval_hfexpr_validif_policy eval_href_validif_policy]. exact Source.
Qed.
Theorem rfa_reset_history_7426 inputs path history limit :
 (forall t, (t < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history t) false (history t) flat_statements = Some (history (S t))) ->
 forall t, (6 <= t)%coq_nat -> (t <= limit)%coq_nat ->
 VM.find 7426 (history t) = Some (Gval (Fuint 32) (rfa_reset_word_28 inputs path)).
Proof.
 intros Steps t Lower Upper. destruct t as [|t]; [lia|].
 apply (rfa_reset_step_7426 inputs path (history t) (history t) (history (S t))).
 - apply (rfa_reset_history_7425 inputs path history limit Steps t);lia.
 - apply Steps;lia.
Qed.
Definition rfa_reset_word_29 inputs path := proj1_sig (formal_symbolic_inputs inputs path (validif_source_address (validif_raw_address nil 8653 0 nil)) nil 32).
Lemma rfa_reset_word_29_size inputs path : size (rfa_reset_word_29 inputs path) = 32%nat.
Proof. exact (proj2_sig (formal_symbolic_inputs inputs path (validif_source_address (validif_raw_address nil 8653 0 nil)) nil 32)). Qed.
Definition rfa_node_8147_expr := (@Evalidif VarOrder.T (@Econst VarOrder.T (Fuint 1) [::false]) (@Econst VarOrder.T (Fuint 32) [::false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false])).
Definition rfa_node_8147_tail := match straight_drop 8654 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma rfa_node_8147_position : straight_drop 8653 flat_statements = Some (@Qcons VarOrder.T (@Snode VarOrder.T 8147 rfa_node_8147_expr) rfa_node_8147_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma rfa_node_8147_safe : formal_typed_suffix_safe flat_memories 8147 rfa_node_8147_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma rfa_node_8147_nonreg : has_register 8147 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem rfa_reset_step_8147 inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 VM.find 8147 result = Some (Gval (Fuint 32) (rfa_reset_word_29 inputs path)).
Proof.
 intros Step.
 eapply formal_combinational_known_node;
 [exact rfa_node_8147_position|exact rfa_node_8147_safe|exact rfa_node_8147_nonreg| |reflexivity|exact Step].
 reflexivity.
Qed.
Theorem rfa_reset_history_8147 inputs path history limit :
 (forall t, (t < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history t) false (history t) flat_statements = Some (history (S t))) ->
 forall t, (1 <= t)%coq_nat -> (t <= limit)%coq_nat ->
 VM.find 8147 (history t) = Some (Gval (Fuint 32) (rfa_reset_word_29 inputs path)).
Proof.
 intros Steps t Lower Upper. destruct t as [|t]; [lia|].
 apply (rfa_reset_step_8147 inputs path (history t) (history t) (history (S t))).
 apply Steps;lia.
Qed.
Definition rfa_node_8148_expr := joint_update_expr_8148.
Theorem rfa_reset_step_8148 inputs path old current result :
 VM.find 8147 old = Some (Gval (Fuint 32) (rfa_reset_word_29 inputs path)) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 VM.find 8148 result = Some (Gval (Fuint 32) (rfa_reset_word_29 inputs path)).
Proof.
 intros Source Step.
 assert (Member : List.In (8148,joint_update_expr_8148) joint_update_expected_nodes).
 { apply (List.nth_error_In joint_update_expected_nodes 1035%nat). vm_compute. reflexivity. }
 destruct (selected_node_safe_position flat_memories flat_statements joint_update_node_offsets flat_statements joint_update_expected_nodes 8148 joint_update_expr_8148 joint_update_node_positions joint_update_node_safety Member) as [count [tail [Position [Safe Nonreg]]]].
 eapply formal_combinational_known_node; [exact Position|exact Safe|exact Nonreg| |reflexivity|exact Step].
 cbn [rfa_node_8148_expr eval_hfexpr_validif_policy eval_href_validif_policy]. exact Source.
Qed.
Theorem rfa_reset_history_8148 inputs path history limit :
 (forall t, (t < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history t) false (history t) flat_statements = Some (history (S t))) ->
 forall t, (2 <= t)%coq_nat -> (t <= limit)%coq_nat ->
 VM.find 8148 (history t) = Some (Gval (Fuint 32) (rfa_reset_word_29 inputs path)).
Proof.
 intros Steps t Lower Upper. destruct t as [|t]; [lia|].
 apply (rfa_reset_step_8148 inputs path (history t) (history t) (history (S t))).
 - apply (rfa_reset_history_8147 inputs path history limit Steps t);lia.
 - apply Steps;lia.
Qed.
Lemma joint_update_connection_816_nonreg : has_register 816 flat_statements = false.
Proof. exact joint_update_connection_816_nonregister. Qed.
Theorem rfa_reset_step_816 inputs path old current result :
 VM.find 8148 old = Some (Gval (Fuint 32) (rfa_reset_word_29 inputs path)) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 VM.find 816 result = Some (Gval (Fuint 32) (rfa_reset_word_29 inputs path)).
Proof.
 intros Source Step.
 apply (declared_connection_value 825 flat_statements joint_update_connection_816_decl joint_update_connection_816_mid joint_update_connection_816_tail 816 8148 32
 (Gval (Fuint 32) (rfa_reset_word_29 inputs path)) (Gval (Fuint 32) (rfa_reset_word_29 inputs path))
 (formal_invalid_policy inputs path) flat_memories old current result joint_update_connection_816_position joint_update_connection_816_split joint_update_connection_816_straight joint_update_connection_816_mid_safe joint_update_connection_816_tail_safe joint_update_connection_816_nonreg (Logic.eq_refl _) Source).
 - assert (Take : take 32 (rfa_reset_word_29 inputs path) = rfa_reset_word_29 inputs path).
   { apply take_oversize. rewrite rfa_reset_word_29_size. reflexivity. }
   cbn [adapt_hvalue_as_type]. rewrite Take. unfold zext_to,zext. rewrite rfa_reset_word_29_size subnn cats0. reflexivity.
 - exact Step.
Qed.
Theorem rfa_reset_history_816 inputs path history limit :
 (forall t, (t < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history t) false (history t) flat_statements = Some (history (S t))) ->
 forall t, (3 <= t)%coq_nat -> (t <= limit)%coq_nat ->
 VM.find 816 (history t) = Some (Gval (Fuint 32) (rfa_reset_word_29 inputs path)).
Proof.
 intros Steps t Lower Upper. destruct t as [|t]; [lia|].
 apply (rfa_reset_step_816 inputs path (history t) (history t) (history (S t))).
 - apply (rfa_reset_history_8148 inputs path history limit Steps t);lia.
 - apply Steps;lia.
Qed.
Definition rfa_node_1114_expr := joint_update_expr_1114.
Theorem rfa_reset_step_1114 inputs path old current result :
 VM.find 816 old = Some (Gval (Fuint 32) (rfa_reset_word_29 inputs path)) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 VM.find 1114 result = Some (Gval (Fuint 32) (rfa_reset_word_29 inputs path)).
Proof.
 intros Source Step.
 assert (Member : List.In (1114,joint_update_expr_1114) joint_update_expected_nodes).
 { apply (List.nth_error_In joint_update_expected_nodes 704%nat). vm_compute. reflexivity. }
 destruct (selected_node_safe_position flat_memories flat_statements joint_update_node_offsets flat_statements joint_update_expected_nodes 1114 joint_update_expr_1114 joint_update_node_positions joint_update_node_safety Member) as [count [tail [Position [Safe Nonreg]]]].
 eapply formal_combinational_known_node; [exact Position|exact Safe|exact Nonreg| |reflexivity|exact Step].
 cbn [rfa_node_1114_expr eval_hfexpr_validif_policy eval_href_validif_policy]. exact Source.
Qed.
Theorem rfa_reset_history_1114 inputs path history limit :
 (forall t, (t < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history t) false (history t) flat_statements = Some (history (S t))) ->
 forall t, (4 <= t)%coq_nat -> (t <= limit)%coq_nat ->
 VM.find 1114 (history t) = Some (Gval (Fuint 32) (rfa_reset_word_29 inputs path)).
Proof.
 intros Steps t Lower Upper. destruct t as [|t]; [lia|].
 apply (rfa_reset_step_1114 inputs path (history t) (history t) (history (S t))).
 - apply (rfa_reset_history_816 inputs path history limit Steps t);lia.
 - apply Steps;lia.
Qed.
Definition rfa_wire_1511_decl := match straight_drop 1591 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition rfa_wire_1511_tail := match straight_drop 9000 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition rfa_wire_1511_mid := take_statements 7408 rfa_wire_1511_decl.
Lemma rfa_wire_1511_position : straight_drop 1590 flat_statements = Some (@Qcons VarOrder.T (@Swire VarOrder.T 1511 (Gtyp (Fuint 32))) rfa_wire_1511_decl).
Proof. vm_compute. reflexivity. Qed.
Lemma rfa_wire_1511_split : rfa_wire_1511_decl = statement_append rfa_wire_1511_mid (@Qcons VarOrder.T (@Sfcnct VarOrder.T (@Eid VarOrder.T 1511) (@Eref VarOrder.T (@Eid VarOrder.T 8148))) rfa_wire_1511_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma rfa_wire_1511_straight : straight_statements rfa_wire_1511_mid.
Proof. vm_compute. exact I. Qed.
Lemma rfa_wire_1511_mid_safe : formal_typed_suffix_safe flat_memories 1511 rfa_wire_1511_mid.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma rfa_wire_1511_tail_safe : formal_typed_suffix_safe flat_memories 1511 rfa_wire_1511_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma rfa_wire_1511_nonreg : has_register 1511 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem rfa_reset_step_1511 inputs path old current result :
 VM.find 8148 old = Some (Gval (Fuint 32) (rfa_reset_word_29 inputs path)) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 VM.find 1511 result = Some (Gval (Fuint 32) (rfa_reset_word_29 inputs path)).
Proof.
 intros Source Step.
 apply (declared_connection_value 1590 flat_statements rfa_wire_1511_decl rfa_wire_1511_mid rfa_wire_1511_tail 1511 8148 32
 (Gval (Fuint 32) (rfa_reset_word_29 inputs path)) (Gval (Fuint 32) (rfa_reset_word_29 inputs path))
 (formal_invalid_policy inputs path) flat_memories old current result rfa_wire_1511_position rfa_wire_1511_split rfa_wire_1511_straight rfa_wire_1511_mid_safe rfa_wire_1511_tail_safe rfa_wire_1511_nonreg (Logic.eq_refl _) Source).
 - assert (Take : take 32 (rfa_reset_word_29 inputs path) = rfa_reset_word_29 inputs path).
   { apply take_oversize. rewrite rfa_reset_word_29_size. reflexivity. }
   cbn [adapt_hvalue_as_type]. rewrite Take. unfold zext_to,zext. rewrite rfa_reset_word_29_size subnn cats0. reflexivity.
 - exact Step.
Qed.
Theorem rfa_reset_history_1511 inputs path history limit :
 (forall t, (t < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history t) false (history t) flat_statements = Some (history (S t))) ->
 forall t, (3 <= t)%coq_nat -> (t <= limit)%coq_nat ->
 VM.find 1511 (history t) = Some (Gval (Fuint 32) (rfa_reset_word_29 inputs path)).
Proof.
 intros Steps t Lower Upper. destruct t as [|t]; [lia|].
 apply (rfa_reset_step_1511 inputs path (history t) (history t) (history (S t))).
 - apply (rfa_reset_history_8148 inputs path history limit Steps t);lia.
 - apply Steps;lia.
Qed.
Definition rfa_wire_1701_decl := match straight_drop 1781 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition rfa_wire_1701_tail := match straight_drop 8252 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition rfa_wire_1701_mid := take_statements 6470 rfa_wire_1701_decl.
Lemma rfa_wire_1701_position : straight_drop 1780 flat_statements = Some (@Qcons VarOrder.T (@Swire VarOrder.T 1701 (Gtyp (Fuint 32))) rfa_wire_1701_decl).
Proof. vm_compute. reflexivity. Qed.
Lemma rfa_wire_1701_split : rfa_wire_1701_decl = statement_append rfa_wire_1701_mid (@Qcons VarOrder.T (@Sfcnct VarOrder.T (@Eid VarOrder.T 1701) (@Eref VarOrder.T (@Eid VarOrder.T 1511))) rfa_wire_1701_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma rfa_wire_1701_straight : straight_statements rfa_wire_1701_mid.
Proof. vm_compute. exact I. Qed.
Lemma rfa_wire_1701_mid_safe : formal_typed_suffix_safe flat_memories 1701 rfa_wire_1701_mid.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma rfa_wire_1701_tail_safe : formal_typed_suffix_safe flat_memories 1701 rfa_wire_1701_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma rfa_wire_1701_nonreg : has_register 1701 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem rfa_reset_step_1701 inputs path old current result :
 VM.find 1511 old = Some (Gval (Fuint 32) (rfa_reset_word_29 inputs path)) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 VM.find 1701 result = Some (Gval (Fuint 32) (rfa_reset_word_29 inputs path)).
Proof.
 intros Source Step.
 apply (declared_connection_value 1780 flat_statements rfa_wire_1701_decl rfa_wire_1701_mid rfa_wire_1701_tail 1701 1511 32
 (Gval (Fuint 32) (rfa_reset_word_29 inputs path)) (Gval (Fuint 32) (rfa_reset_word_29 inputs path))
 (formal_invalid_policy inputs path) flat_memories old current result rfa_wire_1701_position rfa_wire_1701_split rfa_wire_1701_straight rfa_wire_1701_mid_safe rfa_wire_1701_tail_safe rfa_wire_1701_nonreg (Logic.eq_refl _) Source).
 - assert (Take : take 32 (rfa_reset_word_29 inputs path) = rfa_reset_word_29 inputs path).
   { apply take_oversize. rewrite rfa_reset_word_29_size. reflexivity. }
   cbn [adapt_hvalue_as_type]. rewrite Take. unfold zext_to,zext. rewrite rfa_reset_word_29_size subnn cats0. reflexivity.
 - exact Step.
Qed.
Theorem rfa_reset_history_1701 inputs path history limit :
 (forall t, (t < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history t) false (history t) flat_statements = Some (history (S t))) ->
 forall t, (4 <= t)%coq_nat -> (t <= limit)%coq_nat ->
 VM.find 1701 (history t) = Some (Gval (Fuint 32) (rfa_reset_word_29 inputs path)).
Proof.
 intros Steps t Lower Upper. destruct t as [|t]; [lia|].
 apply (rfa_reset_step_1701 inputs path (history t) (history t) (history (S t))).
 - apply (rfa_reset_history_1511 inputs path history limit Steps t);lia.
 - apply Steps;lia.
Qed.
Definition rfa_node_7427_expr := (@Eref VarOrder.T (@Eid VarOrder.T 1701)).
Definition rfa_node_7427_tail := match straight_drop 7599 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma rfa_node_7427_position : straight_drop 7598 flat_statements = Some (@Qcons VarOrder.T (@Snode VarOrder.T 7427 rfa_node_7427_expr) rfa_node_7427_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma rfa_node_7427_safe : formal_typed_suffix_safe flat_memories 7427 rfa_node_7427_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma rfa_node_7427_nonreg : has_register 7427 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem rfa_reset_step_7427 inputs path old current result :
 VM.find 1701 old = Some (Gval (Fuint 32) (rfa_reset_word_29 inputs path)) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 VM.find 7427 result = Some (Gval (Fuint 32) (rfa_reset_word_29 inputs path)).
Proof.
 intros Source Step.
 eapply formal_combinational_known_node;
 [exact rfa_node_7427_position|exact rfa_node_7427_safe|exact rfa_node_7427_nonreg| |reflexivity|exact Step].
 cbn [rfa_node_7427_expr eval_hfexpr_validif_policy eval_href_validif_policy]. exact Source.
Qed.
Theorem rfa_reset_history_7427 inputs path history limit :
 (forall t, (t < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history t) false (history t) flat_statements = Some (history (S t))) ->
 forall t, (5 <= t)%coq_nat -> (t <= limit)%coq_nat ->
 VM.find 7427 (history t) = Some (Gval (Fuint 32) (rfa_reset_word_29 inputs path)).
Proof.
 intros Steps t Lower Upper. destruct t as [|t]; [lia|].
 apply (rfa_reset_step_7427 inputs path (history t) (history t) (history (S t))).
 - apply (rfa_reset_history_1701 inputs path history limit Steps t);lia.
 - apply Steps;lia.
Qed.
Definition rfa_node_7428_expr := (@Eref VarOrder.T (@Eid VarOrder.T 7427)).
Definition rfa_node_7428_tail := match straight_drop 7600 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma rfa_node_7428_position : straight_drop 7599 flat_statements = Some (@Qcons VarOrder.T (@Snode VarOrder.T 7428 rfa_node_7428_expr) rfa_node_7428_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma rfa_node_7428_safe : formal_typed_suffix_safe flat_memories 7428 rfa_node_7428_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma rfa_node_7428_nonreg : has_register 7428 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem rfa_reset_step_7428 inputs path old current result :
 VM.find 7427 old = Some (Gval (Fuint 32) (rfa_reset_word_29 inputs path)) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 VM.find 7428 result = Some (Gval (Fuint 32) (rfa_reset_word_29 inputs path)).
Proof.
 intros Source Step.
 eapply formal_combinational_known_node;
 [exact rfa_node_7428_position|exact rfa_node_7428_safe|exact rfa_node_7428_nonreg| |reflexivity|exact Step].
 cbn [rfa_node_7428_expr eval_hfexpr_validif_policy eval_href_validif_policy]. exact Source.
Qed.
Theorem rfa_reset_history_7428 inputs path history limit :
 (forall t, (t < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history t) false (history t) flat_statements = Some (history (S t))) ->
 forall t, (6 <= t)%coq_nat -> (t <= limit)%coq_nat ->
 VM.find 7428 (history t) = Some (Gval (Fuint 32) (rfa_reset_word_29 inputs path)).
Proof.
 intros Steps t Lower Upper. destruct t as [|t]; [lia|].
 apply (rfa_reset_step_7428 inputs path (history t) (history t) (history (S t))).
 - apply (rfa_reset_history_7427 inputs path history limit Steps t);lia.
 - apply Steps;lia.
Qed.
Definition rfa_reset_word_30 inputs path := proj1_sig (formal_symbolic_inputs inputs path (validif_source_address (validif_raw_address nil 8655 0 nil)) nil 32).
Lemma rfa_reset_word_30_size inputs path : size (rfa_reset_word_30 inputs path) = 32%nat.
Proof. exact (proj2_sig (formal_symbolic_inputs inputs path (validif_source_address (validif_raw_address nil 8655 0 nil)) nil 32)). Qed.
Definition rfa_node_8149_expr := (@Evalidif VarOrder.T (@Econst VarOrder.T (Fuint 1) [::false]) (@Econst VarOrder.T (Fuint 32) [::false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false])).
Definition rfa_node_8149_tail := match straight_drop 8656 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma rfa_node_8149_position : straight_drop 8655 flat_statements = Some (@Qcons VarOrder.T (@Snode VarOrder.T 8149 rfa_node_8149_expr) rfa_node_8149_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma rfa_node_8149_safe : formal_typed_suffix_safe flat_memories 8149 rfa_node_8149_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma rfa_node_8149_nonreg : has_register 8149 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem rfa_reset_step_8149 inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 VM.find 8149 result = Some (Gval (Fuint 32) (rfa_reset_word_30 inputs path)).
Proof.
 intros Step.
 eapply formal_combinational_known_node;
 [exact rfa_node_8149_position|exact rfa_node_8149_safe|exact rfa_node_8149_nonreg| |reflexivity|exact Step].
 reflexivity.
Qed.
Theorem rfa_reset_history_8149 inputs path history limit :
 (forall t, (t < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history t) false (history t) flat_statements = Some (history (S t))) ->
 forall t, (1 <= t)%coq_nat -> (t <= limit)%coq_nat ->
 VM.find 8149 (history t) = Some (Gval (Fuint 32) (rfa_reset_word_30 inputs path)).
Proof.
 intros Steps t Lower Upper. destruct t as [|t]; [lia|].
 apply (rfa_reset_step_8149 inputs path (history t) (history t) (history (S t))).
 apply Steps;lia.
Qed.
Definition rfa_node_8150_expr := joint_update_expr_8150.
Theorem rfa_reset_step_8150 inputs path old current result :
 VM.find 8149 old = Some (Gval (Fuint 32) (rfa_reset_word_30 inputs path)) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 VM.find 8150 result = Some (Gval (Fuint 32) (rfa_reset_word_30 inputs path)).
Proof.
 intros Source Step.
 assert (Member : List.In (8150,joint_update_expr_8150) joint_update_expected_nodes).
 { apply (List.nth_error_In joint_update_expected_nodes 1037%nat). vm_compute. reflexivity. }
 destruct (selected_node_safe_position flat_memories flat_statements joint_update_node_offsets flat_statements joint_update_expected_nodes 8150 joint_update_expr_8150 joint_update_node_positions joint_update_node_safety Member) as [count [tail [Position [Safe Nonreg]]]].
 eapply formal_combinational_known_node; [exact Position|exact Safe|exact Nonreg| |reflexivity|exact Step].
 cbn [rfa_node_8150_expr eval_hfexpr_validif_policy eval_href_validif_policy]. exact Source.
Qed.
Theorem rfa_reset_history_8150 inputs path history limit :
 (forall t, (t < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history t) false (history t) flat_statements = Some (history (S t))) ->
 forall t, (2 <= t)%coq_nat -> (t <= limit)%coq_nat ->
 VM.find 8150 (history t) = Some (Gval (Fuint 32) (rfa_reset_word_30 inputs path)).
Proof.
 intros Steps t Lower Upper. destruct t as [|t]; [lia|].
 apply (rfa_reset_step_8150 inputs path (history t) (history t) (history (S t))).
 - apply (rfa_reset_history_8149 inputs path history limit Steps t);lia.
 - apply Steps;lia.
Qed.
Lemma joint_update_connection_817_nonreg : has_register 817 flat_statements = false.
Proof. exact joint_update_connection_817_nonregister. Qed.
Theorem rfa_reset_step_817 inputs path old current result :
 VM.find 8150 old = Some (Gval (Fuint 32) (rfa_reset_word_30 inputs path)) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 VM.find 817 result = Some (Gval (Fuint 32) (rfa_reset_word_30 inputs path)).
Proof.
 intros Source Step.
 apply (declared_connection_value 826 flat_statements joint_update_connection_817_decl joint_update_connection_817_mid joint_update_connection_817_tail 817 8150 32
 (Gval (Fuint 32) (rfa_reset_word_30 inputs path)) (Gval (Fuint 32) (rfa_reset_word_30 inputs path))
 (formal_invalid_policy inputs path) flat_memories old current result joint_update_connection_817_position joint_update_connection_817_split joint_update_connection_817_straight joint_update_connection_817_mid_safe joint_update_connection_817_tail_safe joint_update_connection_817_nonreg (Logic.eq_refl _) Source).
 - assert (Take : take 32 (rfa_reset_word_30 inputs path) = rfa_reset_word_30 inputs path).
   { apply take_oversize. rewrite rfa_reset_word_30_size. reflexivity. }
   cbn [adapt_hvalue_as_type]. rewrite Take. unfold zext_to,zext. rewrite rfa_reset_word_30_size subnn cats0. reflexivity.
 - exact Step.
Qed.
Theorem rfa_reset_history_817 inputs path history limit :
 (forall t, (t < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history t) false (history t) flat_statements = Some (history (S t))) ->
 forall t, (3 <= t)%coq_nat -> (t <= limit)%coq_nat ->
 VM.find 817 (history t) = Some (Gval (Fuint 32) (rfa_reset_word_30 inputs path)).
Proof.
 intros Steps t Lower Upper. destruct t as [|t]; [lia|].
 apply (rfa_reset_step_817 inputs path (history t) (history t) (history (S t))).
 - apply (rfa_reset_history_8150 inputs path history limit Steps t);lia.
 - apply Steps;lia.
Qed.
Definition rfa_node_1115_expr := joint_update_expr_1115.
Theorem rfa_reset_step_1115 inputs path old current result :
 VM.find 817 old = Some (Gval (Fuint 32) (rfa_reset_word_30 inputs path)) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 VM.find 1115 result = Some (Gval (Fuint 32) (rfa_reset_word_30 inputs path)).
Proof.
 intros Source Step.
 assert (Member : List.In (1115,joint_update_expr_1115) joint_update_expected_nodes).
 { apply (List.nth_error_In joint_update_expected_nodes 705%nat). vm_compute. reflexivity. }
 destruct (selected_node_safe_position flat_memories flat_statements joint_update_node_offsets flat_statements joint_update_expected_nodes 1115 joint_update_expr_1115 joint_update_node_positions joint_update_node_safety Member) as [count [tail [Position [Safe Nonreg]]]].
 eapply formal_combinational_known_node; [exact Position|exact Safe|exact Nonreg| |reflexivity|exact Step].
 cbn [rfa_node_1115_expr eval_hfexpr_validif_policy eval_href_validif_policy]. exact Source.
Qed.
Theorem rfa_reset_history_1115 inputs path history limit :
 (forall t, (t < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history t) false (history t) flat_statements = Some (history (S t))) ->
 forall t, (4 <= t)%coq_nat -> (t <= limit)%coq_nat ->
 VM.find 1115 (history t) = Some (Gval (Fuint 32) (rfa_reset_word_30 inputs path)).
Proof.
 intros Steps t Lower Upper. destruct t as [|t]; [lia|].
 apply (rfa_reset_step_1115 inputs path (history t) (history t) (history (S t))).
 - apply (rfa_reset_history_817 inputs path history limit Steps t);lia.
 - apply Steps;lia.
Qed.
Definition rfa_wire_1512_decl := match straight_drop 1592 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition rfa_wire_1512_tail := match straight_drop 9001 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition rfa_wire_1512_mid := take_statements 7408 rfa_wire_1512_decl.
Lemma rfa_wire_1512_position : straight_drop 1591 flat_statements = Some (@Qcons VarOrder.T (@Swire VarOrder.T 1512 (Gtyp (Fuint 32))) rfa_wire_1512_decl).
Proof. vm_compute. reflexivity. Qed.
Lemma rfa_wire_1512_split : rfa_wire_1512_decl = statement_append rfa_wire_1512_mid (@Qcons VarOrder.T (@Sfcnct VarOrder.T (@Eid VarOrder.T 1512) (@Eref VarOrder.T (@Eid VarOrder.T 8150))) rfa_wire_1512_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma rfa_wire_1512_straight : straight_statements rfa_wire_1512_mid.
Proof. vm_compute. exact I. Qed.
Lemma rfa_wire_1512_mid_safe : formal_typed_suffix_safe flat_memories 1512 rfa_wire_1512_mid.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma rfa_wire_1512_tail_safe : formal_typed_suffix_safe flat_memories 1512 rfa_wire_1512_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma rfa_wire_1512_nonreg : has_register 1512 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem rfa_reset_step_1512 inputs path old current result :
 VM.find 8150 old = Some (Gval (Fuint 32) (rfa_reset_word_30 inputs path)) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 VM.find 1512 result = Some (Gval (Fuint 32) (rfa_reset_word_30 inputs path)).
Proof.
 intros Source Step.
 apply (declared_connection_value 1591 flat_statements rfa_wire_1512_decl rfa_wire_1512_mid rfa_wire_1512_tail 1512 8150 32
 (Gval (Fuint 32) (rfa_reset_word_30 inputs path)) (Gval (Fuint 32) (rfa_reset_word_30 inputs path))
 (formal_invalid_policy inputs path) flat_memories old current result rfa_wire_1512_position rfa_wire_1512_split rfa_wire_1512_straight rfa_wire_1512_mid_safe rfa_wire_1512_tail_safe rfa_wire_1512_nonreg (Logic.eq_refl _) Source).
 - assert (Take : take 32 (rfa_reset_word_30 inputs path) = rfa_reset_word_30 inputs path).
   { apply take_oversize. rewrite rfa_reset_word_30_size. reflexivity. }
   cbn [adapt_hvalue_as_type]. rewrite Take. unfold zext_to,zext. rewrite rfa_reset_word_30_size subnn cats0. reflexivity.
 - exact Step.
Qed.
Theorem rfa_reset_history_1512 inputs path history limit :
 (forall t, (t < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history t) false (history t) flat_statements = Some (history (S t))) ->
 forall t, (3 <= t)%coq_nat -> (t <= limit)%coq_nat ->
 VM.find 1512 (history t) = Some (Gval (Fuint 32) (rfa_reset_word_30 inputs path)).
Proof.
 intros Steps t Lower Upper. destruct t as [|t]; [lia|].
 apply (rfa_reset_step_1512 inputs path (history t) (history t) (history (S t))).
 - apply (rfa_reset_history_8150 inputs path history limit Steps t);lia.
 - apply Steps;lia.
Qed.
Definition rfa_wire_1702_decl := match straight_drop 1782 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition rfa_wire_1702_tail := match straight_drop 8253 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition rfa_wire_1702_mid := take_statements 6470 rfa_wire_1702_decl.
Lemma rfa_wire_1702_position : straight_drop 1781 flat_statements = Some (@Qcons VarOrder.T (@Swire VarOrder.T 1702 (Gtyp (Fuint 32))) rfa_wire_1702_decl).
Proof. vm_compute. reflexivity. Qed.
Lemma rfa_wire_1702_split : rfa_wire_1702_decl = statement_append rfa_wire_1702_mid (@Qcons VarOrder.T (@Sfcnct VarOrder.T (@Eid VarOrder.T 1702) (@Eref VarOrder.T (@Eid VarOrder.T 1512))) rfa_wire_1702_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma rfa_wire_1702_straight : straight_statements rfa_wire_1702_mid.
Proof. vm_compute. exact I. Qed.
Lemma rfa_wire_1702_mid_safe : formal_typed_suffix_safe flat_memories 1702 rfa_wire_1702_mid.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma rfa_wire_1702_tail_safe : formal_typed_suffix_safe flat_memories 1702 rfa_wire_1702_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma rfa_wire_1702_nonreg : has_register 1702 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem rfa_reset_step_1702 inputs path old current result :
 VM.find 1512 old = Some (Gval (Fuint 32) (rfa_reset_word_30 inputs path)) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 VM.find 1702 result = Some (Gval (Fuint 32) (rfa_reset_word_30 inputs path)).
Proof.
 intros Source Step.
 apply (declared_connection_value 1781 flat_statements rfa_wire_1702_decl rfa_wire_1702_mid rfa_wire_1702_tail 1702 1512 32
 (Gval (Fuint 32) (rfa_reset_word_30 inputs path)) (Gval (Fuint 32) (rfa_reset_word_30 inputs path))
 (formal_invalid_policy inputs path) flat_memories old current result rfa_wire_1702_position rfa_wire_1702_split rfa_wire_1702_straight rfa_wire_1702_mid_safe rfa_wire_1702_tail_safe rfa_wire_1702_nonreg (Logic.eq_refl _) Source).
 - assert (Take : take 32 (rfa_reset_word_30 inputs path) = rfa_reset_word_30 inputs path).
   { apply take_oversize. rewrite rfa_reset_word_30_size. reflexivity. }
   cbn [adapt_hvalue_as_type]. rewrite Take. unfold zext_to,zext. rewrite rfa_reset_word_30_size subnn cats0. reflexivity.
 - exact Step.
Qed.
Theorem rfa_reset_history_1702 inputs path history limit :
 (forall t, (t < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history t) false (history t) flat_statements = Some (history (S t))) ->
 forall t, (4 <= t)%coq_nat -> (t <= limit)%coq_nat ->
 VM.find 1702 (history t) = Some (Gval (Fuint 32) (rfa_reset_word_30 inputs path)).
Proof.
 intros Steps t Lower Upper. destruct t as [|t]; [lia|].
 apply (rfa_reset_step_1702 inputs path (history t) (history t) (history (S t))).
 - apply (rfa_reset_history_1512 inputs path history limit Steps t);lia.
 - apply Steps;lia.
Qed.
Definition rfa_node_7429_expr := (@Eref VarOrder.T (@Eid VarOrder.T 1702)).
Definition rfa_node_7429_tail := match straight_drop 7601 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma rfa_node_7429_position : straight_drop 7600 flat_statements = Some (@Qcons VarOrder.T (@Snode VarOrder.T 7429 rfa_node_7429_expr) rfa_node_7429_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma rfa_node_7429_safe : formal_typed_suffix_safe flat_memories 7429 rfa_node_7429_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma rfa_node_7429_nonreg : has_register 7429 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem rfa_reset_step_7429 inputs path old current result :
 VM.find 1702 old = Some (Gval (Fuint 32) (rfa_reset_word_30 inputs path)) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 VM.find 7429 result = Some (Gval (Fuint 32) (rfa_reset_word_30 inputs path)).
Proof.
 intros Source Step.
 eapply formal_combinational_known_node;
 [exact rfa_node_7429_position|exact rfa_node_7429_safe|exact rfa_node_7429_nonreg| |reflexivity|exact Step].
 cbn [rfa_node_7429_expr eval_hfexpr_validif_policy eval_href_validif_policy]. exact Source.
Qed.
Theorem rfa_reset_history_7429 inputs path history limit :
 (forall t, (t < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history t) false (history t) flat_statements = Some (history (S t))) ->
 forall t, (5 <= t)%coq_nat -> (t <= limit)%coq_nat ->
 VM.find 7429 (history t) = Some (Gval (Fuint 32) (rfa_reset_word_30 inputs path)).
Proof.
 intros Steps t Lower Upper. destruct t as [|t]; [lia|].
 apply (rfa_reset_step_7429 inputs path (history t) (history t) (history (S t))).
 - apply (rfa_reset_history_1702 inputs path history limit Steps t);lia.
 - apply Steps;lia.
Qed.
Definition rfa_node_7430_expr := (@Eref VarOrder.T (@Eid VarOrder.T 7429)).
Definition rfa_node_7430_tail := match straight_drop 7602 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma rfa_node_7430_position : straight_drop 7601 flat_statements = Some (@Qcons VarOrder.T (@Snode VarOrder.T 7430 rfa_node_7430_expr) rfa_node_7430_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma rfa_node_7430_safe : formal_typed_suffix_safe flat_memories 7430 rfa_node_7430_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma rfa_node_7430_nonreg : has_register 7430 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem rfa_reset_step_7430 inputs path old current result :
 VM.find 7429 old = Some (Gval (Fuint 32) (rfa_reset_word_30 inputs path)) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 VM.find 7430 result = Some (Gval (Fuint 32) (rfa_reset_word_30 inputs path)).
Proof.
 intros Source Step.
 eapply formal_combinational_known_node;
 [exact rfa_node_7430_position|exact rfa_node_7430_safe|exact rfa_node_7430_nonreg| |reflexivity|exact Step].
 cbn [rfa_node_7430_expr eval_hfexpr_validif_policy eval_href_validif_policy]. exact Source.
Qed.
Theorem rfa_reset_history_7430 inputs path history limit :
 (forall t, (t < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history t) false (history t) flat_statements = Some (history (S t))) ->
 forall t, (6 <= t)%coq_nat -> (t <= limit)%coq_nat ->
 VM.find 7430 (history t) = Some (Gval (Fuint 32) (rfa_reset_word_30 inputs path)).
Proof.
 intros Steps t Lower Upper. destruct t as [|t]; [lia|].
 apply (rfa_reset_step_7430 inputs path (history t) (history t) (history (S t))).
 - apply (rfa_reset_history_7429 inputs path history limit Steps t);lia.
 - apply Steps;lia.
Qed.
Definition rfa_reset_word_31 inputs path := proj1_sig (formal_symbolic_inputs inputs path (validif_source_address (validif_raw_address nil 8657 0 nil)) nil 32).
Lemma rfa_reset_word_31_size inputs path : size (rfa_reset_word_31 inputs path) = 32%nat.
Proof. exact (proj2_sig (formal_symbolic_inputs inputs path (validif_source_address (validif_raw_address nil 8657 0 nil)) nil 32)). Qed.
Definition rfa_node_8151_expr := (@Evalidif VarOrder.T (@Econst VarOrder.T (Fuint 1) [::false]) (@Econst VarOrder.T (Fuint 32) [::false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false])).
Definition rfa_node_8151_tail := match straight_drop 8658 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma rfa_node_8151_position : straight_drop 8657 flat_statements = Some (@Qcons VarOrder.T (@Snode VarOrder.T 8151 rfa_node_8151_expr) rfa_node_8151_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma rfa_node_8151_safe : formal_typed_suffix_safe flat_memories 8151 rfa_node_8151_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma rfa_node_8151_nonreg : has_register 8151 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem rfa_reset_step_8151 inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 VM.find 8151 result = Some (Gval (Fuint 32) (rfa_reset_word_31 inputs path)).
Proof.
 intros Step.
 eapply formal_combinational_known_node;
 [exact rfa_node_8151_position|exact rfa_node_8151_safe|exact rfa_node_8151_nonreg| |reflexivity|exact Step].
 reflexivity.
Qed.
Theorem rfa_reset_history_8151 inputs path history limit :
 (forall t, (t < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history t) false (history t) flat_statements = Some (history (S t))) ->
 forall t, (1 <= t)%coq_nat -> (t <= limit)%coq_nat ->
 VM.find 8151 (history t) = Some (Gval (Fuint 32) (rfa_reset_word_31 inputs path)).
Proof.
 intros Steps t Lower Upper. destruct t as [|t]; [lia|].
 apply (rfa_reset_step_8151 inputs path (history t) (history t) (history (S t))).
 apply Steps;lia.
Qed.
Definition rfa_node_8152_expr := joint_update_expr_8152.
Theorem rfa_reset_step_8152 inputs path old current result :
 VM.find 8151 old = Some (Gval (Fuint 32) (rfa_reset_word_31 inputs path)) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 VM.find 8152 result = Some (Gval (Fuint 32) (rfa_reset_word_31 inputs path)).
Proof.
 intros Source Step.
 assert (Member : List.In (8152,joint_update_expr_8152) joint_update_expected_nodes).
 { apply (List.nth_error_In joint_update_expected_nodes 1039%nat). vm_compute. reflexivity. }
 destruct (selected_node_safe_position flat_memories flat_statements joint_update_node_offsets flat_statements joint_update_expected_nodes 8152 joint_update_expr_8152 joint_update_node_positions joint_update_node_safety Member) as [count [tail [Position [Safe Nonreg]]]].
 eapply formal_combinational_known_node; [exact Position|exact Safe|exact Nonreg| |reflexivity|exact Step].
 cbn [rfa_node_8152_expr eval_hfexpr_validif_policy eval_href_validif_policy]. exact Source.
Qed.
Theorem rfa_reset_history_8152 inputs path history limit :
 (forall t, (t < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history t) false (history t) flat_statements = Some (history (S t))) ->
 forall t, (2 <= t)%coq_nat -> (t <= limit)%coq_nat ->
 VM.find 8152 (history t) = Some (Gval (Fuint 32) (rfa_reset_word_31 inputs path)).
Proof.
 intros Steps t Lower Upper. destruct t as [|t]; [lia|].
 apply (rfa_reset_step_8152 inputs path (history t) (history t) (history (S t))).
 - apply (rfa_reset_history_8151 inputs path history limit Steps t);lia.
 - apply Steps;lia.
Qed.
Lemma joint_update_connection_818_nonreg : has_register 818 flat_statements = false.
Proof. exact joint_update_connection_818_nonregister. Qed.
Theorem rfa_reset_step_818 inputs path old current result :
 VM.find 8152 old = Some (Gval (Fuint 32) (rfa_reset_word_31 inputs path)) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 VM.find 818 result = Some (Gval (Fuint 32) (rfa_reset_word_31 inputs path)).
Proof.
 intros Source Step.
 apply (declared_connection_value 827 flat_statements joint_update_connection_818_decl joint_update_connection_818_mid joint_update_connection_818_tail 818 8152 32
 (Gval (Fuint 32) (rfa_reset_word_31 inputs path)) (Gval (Fuint 32) (rfa_reset_word_31 inputs path))
 (formal_invalid_policy inputs path) flat_memories old current result joint_update_connection_818_position joint_update_connection_818_split joint_update_connection_818_straight joint_update_connection_818_mid_safe joint_update_connection_818_tail_safe joint_update_connection_818_nonreg (Logic.eq_refl _) Source).
 - assert (Take : take 32 (rfa_reset_word_31 inputs path) = rfa_reset_word_31 inputs path).
   { apply take_oversize. rewrite rfa_reset_word_31_size. reflexivity. }
   cbn [adapt_hvalue_as_type]. rewrite Take. unfold zext_to,zext. rewrite rfa_reset_word_31_size subnn cats0. reflexivity.
 - exact Step.
Qed.
Theorem rfa_reset_history_818 inputs path history limit :
 (forall t, (t < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history t) false (history t) flat_statements = Some (history (S t))) ->
 forall t, (3 <= t)%coq_nat -> (t <= limit)%coq_nat ->
 VM.find 818 (history t) = Some (Gval (Fuint 32) (rfa_reset_word_31 inputs path)).
Proof.
 intros Steps t Lower Upper. destruct t as [|t]; [lia|].
 apply (rfa_reset_step_818 inputs path (history t) (history t) (history (S t))).
 - apply (rfa_reset_history_8152 inputs path history limit Steps t);lia.
 - apply Steps;lia.
Qed.
Definition rfa_node_1116_expr := joint_update_expr_1116.
Theorem rfa_reset_step_1116 inputs path old current result :
 VM.find 818 old = Some (Gval (Fuint 32) (rfa_reset_word_31 inputs path)) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 VM.find 1116 result = Some (Gval (Fuint 32) (rfa_reset_word_31 inputs path)).
Proof.
 intros Source Step.
 assert (Member : List.In (1116,joint_update_expr_1116) joint_update_expected_nodes).
 { apply (List.nth_error_In joint_update_expected_nodes 706%nat). vm_compute. reflexivity. }
 destruct (selected_node_safe_position flat_memories flat_statements joint_update_node_offsets flat_statements joint_update_expected_nodes 1116 joint_update_expr_1116 joint_update_node_positions joint_update_node_safety Member) as [count [tail [Position [Safe Nonreg]]]].
 eapply formal_combinational_known_node; [exact Position|exact Safe|exact Nonreg| |reflexivity|exact Step].
 cbn [rfa_node_1116_expr eval_hfexpr_validif_policy eval_href_validif_policy]. exact Source.
Qed.
Theorem rfa_reset_history_1116 inputs path history limit :
 (forall t, (t < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history t) false (history t) flat_statements = Some (history (S t))) ->
 forall t, (4 <= t)%coq_nat -> (t <= limit)%coq_nat ->
 VM.find 1116 (history t) = Some (Gval (Fuint 32) (rfa_reset_word_31 inputs path)).
Proof.
 intros Steps t Lower Upper. destruct t as [|t]; [lia|].
 apply (rfa_reset_step_1116 inputs path (history t) (history t) (history (S t))).
 - apply (rfa_reset_history_818 inputs path history limit Steps t);lia.
 - apply Steps;lia.
Qed.
Definition rfa_wire_1513_decl := match straight_drop 1593 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition rfa_wire_1513_tail := match straight_drop 9002 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition rfa_wire_1513_mid := take_statements 7408 rfa_wire_1513_decl.
Lemma rfa_wire_1513_position : straight_drop 1592 flat_statements = Some (@Qcons VarOrder.T (@Swire VarOrder.T 1513 (Gtyp (Fuint 32))) rfa_wire_1513_decl).
Proof. vm_compute. reflexivity. Qed.
Lemma rfa_wire_1513_split : rfa_wire_1513_decl = statement_append rfa_wire_1513_mid (@Qcons VarOrder.T (@Sfcnct VarOrder.T (@Eid VarOrder.T 1513) (@Eref VarOrder.T (@Eid VarOrder.T 8152))) rfa_wire_1513_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma rfa_wire_1513_straight : straight_statements rfa_wire_1513_mid.
Proof. vm_compute. exact I. Qed.
Lemma rfa_wire_1513_mid_safe : formal_typed_suffix_safe flat_memories 1513 rfa_wire_1513_mid.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma rfa_wire_1513_tail_safe : formal_typed_suffix_safe flat_memories 1513 rfa_wire_1513_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma rfa_wire_1513_nonreg : has_register 1513 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem rfa_reset_step_1513 inputs path old current result :
 VM.find 8152 old = Some (Gval (Fuint 32) (rfa_reset_word_31 inputs path)) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 VM.find 1513 result = Some (Gval (Fuint 32) (rfa_reset_word_31 inputs path)).
Proof.
 intros Source Step.
 apply (declared_connection_value 1592 flat_statements rfa_wire_1513_decl rfa_wire_1513_mid rfa_wire_1513_tail 1513 8152 32
 (Gval (Fuint 32) (rfa_reset_word_31 inputs path)) (Gval (Fuint 32) (rfa_reset_word_31 inputs path))
 (formal_invalid_policy inputs path) flat_memories old current result rfa_wire_1513_position rfa_wire_1513_split rfa_wire_1513_straight rfa_wire_1513_mid_safe rfa_wire_1513_tail_safe rfa_wire_1513_nonreg (Logic.eq_refl _) Source).
 - assert (Take : take 32 (rfa_reset_word_31 inputs path) = rfa_reset_word_31 inputs path).
   { apply take_oversize. rewrite rfa_reset_word_31_size. reflexivity. }
   cbn [adapt_hvalue_as_type]. rewrite Take. unfold zext_to,zext. rewrite rfa_reset_word_31_size subnn cats0. reflexivity.
 - exact Step.
Qed.
Theorem rfa_reset_history_1513 inputs path history limit :
 (forall t, (t < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history t) false (history t) flat_statements = Some (history (S t))) ->
 forall t, (3 <= t)%coq_nat -> (t <= limit)%coq_nat ->
 VM.find 1513 (history t) = Some (Gval (Fuint 32) (rfa_reset_word_31 inputs path)).
Proof.
 intros Steps t Lower Upper. destruct t as [|t]; [lia|].
 apply (rfa_reset_step_1513 inputs path (history t) (history t) (history (S t))).
 - apply (rfa_reset_history_8152 inputs path history limit Steps t);lia.
 - apply Steps;lia.
Qed.
Definition rfa_wire_1703_decl := match straight_drop 1783 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition rfa_wire_1703_tail := match straight_drop 8254 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition rfa_wire_1703_mid := take_statements 6470 rfa_wire_1703_decl.
Lemma rfa_wire_1703_position : straight_drop 1782 flat_statements = Some (@Qcons VarOrder.T (@Swire VarOrder.T 1703 (Gtyp (Fuint 32))) rfa_wire_1703_decl).
Proof. vm_compute. reflexivity. Qed.
Lemma rfa_wire_1703_split : rfa_wire_1703_decl = statement_append rfa_wire_1703_mid (@Qcons VarOrder.T (@Sfcnct VarOrder.T (@Eid VarOrder.T 1703) (@Eref VarOrder.T (@Eid VarOrder.T 1513))) rfa_wire_1703_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma rfa_wire_1703_straight : straight_statements rfa_wire_1703_mid.
Proof. vm_compute. exact I. Qed.
Lemma rfa_wire_1703_mid_safe : formal_typed_suffix_safe flat_memories 1703 rfa_wire_1703_mid.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma rfa_wire_1703_tail_safe : formal_typed_suffix_safe flat_memories 1703 rfa_wire_1703_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma rfa_wire_1703_nonreg : has_register 1703 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem rfa_reset_step_1703 inputs path old current result :
 VM.find 1513 old = Some (Gval (Fuint 32) (rfa_reset_word_31 inputs path)) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 VM.find 1703 result = Some (Gval (Fuint 32) (rfa_reset_word_31 inputs path)).
Proof.
 intros Source Step.
 apply (declared_connection_value 1782 flat_statements rfa_wire_1703_decl rfa_wire_1703_mid rfa_wire_1703_tail 1703 1513 32
 (Gval (Fuint 32) (rfa_reset_word_31 inputs path)) (Gval (Fuint 32) (rfa_reset_word_31 inputs path))
 (formal_invalid_policy inputs path) flat_memories old current result rfa_wire_1703_position rfa_wire_1703_split rfa_wire_1703_straight rfa_wire_1703_mid_safe rfa_wire_1703_tail_safe rfa_wire_1703_nonreg (Logic.eq_refl _) Source).
 - assert (Take : take 32 (rfa_reset_word_31 inputs path) = rfa_reset_word_31 inputs path).
   { apply take_oversize. rewrite rfa_reset_word_31_size. reflexivity. }
   cbn [adapt_hvalue_as_type]. rewrite Take. unfold zext_to,zext. rewrite rfa_reset_word_31_size subnn cats0. reflexivity.
 - exact Step.
Qed.
Theorem rfa_reset_history_1703 inputs path history limit :
 (forall t, (t < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history t) false (history t) flat_statements = Some (history (S t))) ->
 forall t, (4 <= t)%coq_nat -> (t <= limit)%coq_nat ->
 VM.find 1703 (history t) = Some (Gval (Fuint 32) (rfa_reset_word_31 inputs path)).
Proof.
 intros Steps t Lower Upper. destruct t as [|t]; [lia|].
 apply (rfa_reset_step_1703 inputs path (history t) (history t) (history (S t))).
 - apply (rfa_reset_history_1513 inputs path history limit Steps t);lia.
 - apply Steps;lia.
Qed.
Definition rfa_node_7431_expr := (@Eref VarOrder.T (@Eid VarOrder.T 1703)).
Definition rfa_node_7431_tail := match straight_drop 7603 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma rfa_node_7431_position : straight_drop 7602 flat_statements = Some (@Qcons VarOrder.T (@Snode VarOrder.T 7431 rfa_node_7431_expr) rfa_node_7431_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma rfa_node_7431_safe : formal_typed_suffix_safe flat_memories 7431 rfa_node_7431_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma rfa_node_7431_nonreg : has_register 7431 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem rfa_reset_step_7431 inputs path old current result :
 VM.find 1703 old = Some (Gval (Fuint 32) (rfa_reset_word_31 inputs path)) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 VM.find 7431 result = Some (Gval (Fuint 32) (rfa_reset_word_31 inputs path)).
Proof.
 intros Source Step.
 eapply formal_combinational_known_node;
 [exact rfa_node_7431_position|exact rfa_node_7431_safe|exact rfa_node_7431_nonreg| |reflexivity|exact Step].
 cbn [rfa_node_7431_expr eval_hfexpr_validif_policy eval_href_validif_policy]. exact Source.
Qed.
Theorem rfa_reset_history_7431 inputs path history limit :
 (forall t, (t < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history t) false (history t) flat_statements = Some (history (S t))) ->
 forall t, (5 <= t)%coq_nat -> (t <= limit)%coq_nat ->
 VM.find 7431 (history t) = Some (Gval (Fuint 32) (rfa_reset_word_31 inputs path)).
Proof.
 intros Steps t Lower Upper. destruct t as [|t]; [lia|].
 apply (rfa_reset_step_7431 inputs path (history t) (history t) (history (S t))).
 - apply (rfa_reset_history_1703 inputs path history limit Steps t);lia.
 - apply Steps;lia.
Qed.
Definition rfa_node_7432_expr := (@Eref VarOrder.T (@Eid VarOrder.T 7431)).
Definition rfa_node_7432_tail := match straight_drop 7604 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma rfa_node_7432_position : straight_drop 7603 flat_statements = Some (@Qcons VarOrder.T (@Snode VarOrder.T 7432 rfa_node_7432_expr) rfa_node_7432_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma rfa_node_7432_safe : formal_typed_suffix_safe flat_memories 7432 rfa_node_7432_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma rfa_node_7432_nonreg : has_register 7432 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem rfa_reset_step_7432 inputs path old current result :
 VM.find 7431 old = Some (Gval (Fuint 32) (rfa_reset_word_31 inputs path)) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 VM.find 7432 result = Some (Gval (Fuint 32) (rfa_reset_word_31 inputs path)).
Proof.
 intros Source Step.
 eapply formal_combinational_known_node;
 [exact rfa_node_7432_position|exact rfa_node_7432_safe|exact rfa_node_7432_nonreg| |reflexivity|exact Step].
 cbn [rfa_node_7432_expr eval_hfexpr_validif_policy eval_href_validif_policy]. exact Source.
Qed.
Theorem rfa_reset_history_7432 inputs path history limit :
 (forall t, (t < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history t) false (history t) flat_statements = Some (history (S t))) ->
 forall t, (6 <= t)%coq_nat -> (t <= limit)%coq_nat ->
 VM.find 7432 (history t) = Some (Gval (Fuint 32) (rfa_reset_word_31 inputs path)).
Proof.
 intros Steps t Lower Upper. destruct t as [|t]; [lia|].
 apply (rfa_reset_step_7432 inputs path (history t) (history t) (history (S t))).
 - apply (rfa_reset_history_7431 inputs path history limit Steps t);lia.
 - apply Steps;lia.
Qed.
