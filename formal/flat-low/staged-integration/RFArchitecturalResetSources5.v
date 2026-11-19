Require Import SelectedNodeSafety JointUpdateNodePositions JointUpdateExpressionCertificates JointUpdateConnectionCertificates CoreSocModel ComparisonNodes ScalarNodeFrames FormalTypedNodeFrames RegisterInvariants FormalTypedNodeEquation FormalDeclaredConnection FormalStatementSegments RegisterCommitCertificate FormalUIntRegisterCommitSource SelectedUIntMuxIdentity UIntResizeRoundtrip.
From Coq Require Import ZArith List Lia.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From nbits Require Import NBits.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Definition rfa_reset_word_20 inputs path := proj1_sig (formal_symbolic_inputs inputs path (validif_source_address (validif_raw_address nil 8635 0 nil)) nil 32).
Lemma rfa_reset_word_20_size inputs path : size (rfa_reset_word_20 inputs path) = 32%nat.
Proof. exact (proj2_sig (formal_symbolic_inputs inputs path (validif_source_address (validif_raw_address nil 8635 0 nil)) nil 32)). Qed.
Definition rfa_node_8129_expr := (@Evalidif VarOrder.T (@Econst VarOrder.T (Fuint 1) [::false]) (@Econst VarOrder.T (Fuint 32) [::false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false])).
Definition rfa_node_8129_tail := match straight_drop 8636 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma rfa_node_8129_position : straight_drop 8635 flat_statements = Some (@Qcons VarOrder.T (@Snode VarOrder.T 8129 rfa_node_8129_expr) rfa_node_8129_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma rfa_node_8129_safe : formal_typed_suffix_safe flat_memories 8129 rfa_node_8129_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma rfa_node_8129_nonreg : has_register 8129 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem rfa_reset_step_8129 inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 VM.find 8129 result = Some (Gval (Fuint 32) (rfa_reset_word_20 inputs path)).
Proof.
 intros Step.
 eapply formal_combinational_known_node;
 [exact rfa_node_8129_position|exact rfa_node_8129_safe|exact rfa_node_8129_nonreg| |reflexivity|exact Step].
 reflexivity.
Qed.
Theorem rfa_reset_history_8129 inputs path history limit :
 (forall t, (t < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history t) false (history t) flat_statements = Some (history (S t))) ->
 forall t, (1 <= t)%coq_nat -> (t <= limit)%coq_nat ->
 VM.find 8129 (history t) = Some (Gval (Fuint 32) (rfa_reset_word_20 inputs path)).
Proof.
 intros Steps t Lower Upper. destruct t as [|t]; [lia|].
 apply (rfa_reset_step_8129 inputs path (history t) (history t) (history (S t))).
 apply Steps;lia.
Qed.
Definition rfa_node_8130_expr := joint_update_expr_8130.
Theorem rfa_reset_step_8130 inputs path old current result :
 VM.find 8129 old = Some (Gval (Fuint 32) (rfa_reset_word_20 inputs path)) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 VM.find 8130 result = Some (Gval (Fuint 32) (rfa_reset_word_20 inputs path)).
Proof.
 intros Source Step.
 assert (Member : List.In (8130,joint_update_expr_8130) joint_update_expected_nodes).
 { apply (List.nth_error_In joint_update_expected_nodes 1017%nat). vm_compute. reflexivity. }
 destruct (selected_node_safe_position flat_memories flat_statements joint_update_node_offsets flat_statements joint_update_expected_nodes 8130 joint_update_expr_8130 joint_update_node_positions joint_update_node_safety Member) as [count [tail [Position [Safe Nonreg]]]].
 eapply formal_combinational_known_node; [exact Position|exact Safe|exact Nonreg| |reflexivity|exact Step].
 cbn [rfa_node_8130_expr eval_hfexpr_validif_policy eval_href_validif_policy]. exact Source.
Qed.
Theorem rfa_reset_history_8130 inputs path history limit :
 (forall t, (t < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history t) false (history t) flat_statements = Some (history (S t))) ->
 forall t, (2 <= t)%coq_nat -> (t <= limit)%coq_nat ->
 VM.find 8130 (history t) = Some (Gval (Fuint 32) (rfa_reset_word_20 inputs path)).
Proof.
 intros Steps t Lower Upper. destruct t as [|t]; [lia|].
 apply (rfa_reset_step_8130 inputs path (history t) (history t) (history (S t))).
 - apply (rfa_reset_history_8129 inputs path history limit Steps t);lia.
 - apply Steps;lia.
Qed.
Lemma joint_update_connection_807_nonreg : has_register 807 flat_statements = false.
Proof. exact joint_update_connection_807_nonregister. Qed.
Theorem rfa_reset_step_807 inputs path old current result :
 VM.find 8130 old = Some (Gval (Fuint 32) (rfa_reset_word_20 inputs path)) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 VM.find 807 result = Some (Gval (Fuint 32) (rfa_reset_word_20 inputs path)).
Proof.
 intros Source Step.
 apply (declared_connection_value 816 flat_statements joint_update_connection_807_decl joint_update_connection_807_mid joint_update_connection_807_tail 807 8130 32
 (Gval (Fuint 32) (rfa_reset_word_20 inputs path)) (Gval (Fuint 32) (rfa_reset_word_20 inputs path))
 (formal_invalid_policy inputs path) flat_memories old current result joint_update_connection_807_position joint_update_connection_807_split joint_update_connection_807_straight joint_update_connection_807_mid_safe joint_update_connection_807_tail_safe joint_update_connection_807_nonreg (Logic.eq_refl _) Source).
 - assert (Take : take 32 (rfa_reset_word_20 inputs path) = rfa_reset_word_20 inputs path).
   { apply take_oversize. rewrite rfa_reset_word_20_size. reflexivity. }
   cbn [adapt_hvalue_as_type]. rewrite Take. unfold zext_to,zext. rewrite rfa_reset_word_20_size subnn cats0. reflexivity.
 - exact Step.
Qed.
Theorem rfa_reset_history_807 inputs path history limit :
 (forall t, (t < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history t) false (history t) flat_statements = Some (history (S t))) ->
 forall t, (3 <= t)%coq_nat -> (t <= limit)%coq_nat ->
 VM.find 807 (history t) = Some (Gval (Fuint 32) (rfa_reset_word_20 inputs path)).
Proof.
 intros Steps t Lower Upper. destruct t as [|t]; [lia|].
 apply (rfa_reset_step_807 inputs path (history t) (history t) (history (S t))).
 - apply (rfa_reset_history_8130 inputs path history limit Steps t);lia.
 - apply Steps;lia.
Qed.
Definition rfa_node_1105_expr := joint_update_expr_1105.
Theorem rfa_reset_step_1105 inputs path old current result :
 VM.find 807 old = Some (Gval (Fuint 32) (rfa_reset_word_20 inputs path)) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 VM.find 1105 result = Some (Gval (Fuint 32) (rfa_reset_word_20 inputs path)).
Proof.
 intros Source Step.
 assert (Member : List.In (1105,joint_update_expr_1105) joint_update_expected_nodes).
 { apply (List.nth_error_In joint_update_expected_nodes 695%nat). vm_compute. reflexivity. }
 destruct (selected_node_safe_position flat_memories flat_statements joint_update_node_offsets flat_statements joint_update_expected_nodes 1105 joint_update_expr_1105 joint_update_node_positions joint_update_node_safety Member) as [count [tail [Position [Safe Nonreg]]]].
 eapply formal_combinational_known_node; [exact Position|exact Safe|exact Nonreg| |reflexivity|exact Step].
 cbn [rfa_node_1105_expr eval_hfexpr_validif_policy eval_href_validif_policy]. exact Source.
Qed.
Theorem rfa_reset_history_1105 inputs path history limit :
 (forall t, (t < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history t) false (history t) flat_statements = Some (history (S t))) ->
 forall t, (4 <= t)%coq_nat -> (t <= limit)%coq_nat ->
 VM.find 1105 (history t) = Some (Gval (Fuint 32) (rfa_reset_word_20 inputs path)).
Proof.
 intros Steps t Lower Upper. destruct t as [|t]; [lia|].
 apply (rfa_reset_step_1105 inputs path (history t) (history t) (history (S t))).
 - apply (rfa_reset_history_807 inputs path history limit Steps t);lia.
 - apply Steps;lia.
Qed.
Definition rfa_wire_1502_decl := match straight_drop 1582 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition rfa_wire_1502_tail := match straight_drop 8991 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition rfa_wire_1502_mid := take_statements 7408 rfa_wire_1502_decl.
Lemma rfa_wire_1502_position : straight_drop 1581 flat_statements = Some (@Qcons VarOrder.T (@Swire VarOrder.T 1502 (Gtyp (Fuint 32))) rfa_wire_1502_decl).
Proof. vm_compute. reflexivity. Qed.
Lemma rfa_wire_1502_split : rfa_wire_1502_decl = statement_append rfa_wire_1502_mid (@Qcons VarOrder.T (@Sfcnct VarOrder.T (@Eid VarOrder.T 1502) (@Eref VarOrder.T (@Eid VarOrder.T 8130))) rfa_wire_1502_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma rfa_wire_1502_straight : straight_statements rfa_wire_1502_mid.
Proof. vm_compute. exact I. Qed.
Lemma rfa_wire_1502_mid_safe : formal_typed_suffix_safe flat_memories 1502 rfa_wire_1502_mid.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma rfa_wire_1502_tail_safe : formal_typed_suffix_safe flat_memories 1502 rfa_wire_1502_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma rfa_wire_1502_nonreg : has_register 1502 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem rfa_reset_step_1502 inputs path old current result :
 VM.find 8130 old = Some (Gval (Fuint 32) (rfa_reset_word_20 inputs path)) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 VM.find 1502 result = Some (Gval (Fuint 32) (rfa_reset_word_20 inputs path)).
Proof.
 intros Source Step.
 apply (declared_connection_value 1581 flat_statements rfa_wire_1502_decl rfa_wire_1502_mid rfa_wire_1502_tail 1502 8130 32
 (Gval (Fuint 32) (rfa_reset_word_20 inputs path)) (Gval (Fuint 32) (rfa_reset_word_20 inputs path))
 (formal_invalid_policy inputs path) flat_memories old current result rfa_wire_1502_position rfa_wire_1502_split rfa_wire_1502_straight rfa_wire_1502_mid_safe rfa_wire_1502_tail_safe rfa_wire_1502_nonreg (Logic.eq_refl _) Source).
 - assert (Take : take 32 (rfa_reset_word_20 inputs path) = rfa_reset_word_20 inputs path).
   { apply take_oversize. rewrite rfa_reset_word_20_size. reflexivity. }
   cbn [adapt_hvalue_as_type]. rewrite Take. unfold zext_to,zext. rewrite rfa_reset_word_20_size subnn cats0. reflexivity.
 - exact Step.
Qed.
Theorem rfa_reset_history_1502 inputs path history limit :
 (forall t, (t < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history t) false (history t) flat_statements = Some (history (S t))) ->
 forall t, (3 <= t)%coq_nat -> (t <= limit)%coq_nat ->
 VM.find 1502 (history t) = Some (Gval (Fuint 32) (rfa_reset_word_20 inputs path)).
Proof.
 intros Steps t Lower Upper. destruct t as [|t]; [lia|].
 apply (rfa_reset_step_1502 inputs path (history t) (history t) (history (S t))).
 - apply (rfa_reset_history_8130 inputs path history limit Steps t);lia.
 - apply Steps;lia.
Qed.
Definition rfa_wire_1692_decl := match straight_drop 1772 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition rfa_wire_1692_tail := match straight_drop 8243 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition rfa_wire_1692_mid := take_statements 6470 rfa_wire_1692_decl.
Lemma rfa_wire_1692_position : straight_drop 1771 flat_statements = Some (@Qcons VarOrder.T (@Swire VarOrder.T 1692 (Gtyp (Fuint 32))) rfa_wire_1692_decl).
Proof. vm_compute. reflexivity. Qed.
Lemma rfa_wire_1692_split : rfa_wire_1692_decl = statement_append rfa_wire_1692_mid (@Qcons VarOrder.T (@Sfcnct VarOrder.T (@Eid VarOrder.T 1692) (@Eref VarOrder.T (@Eid VarOrder.T 1502))) rfa_wire_1692_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma rfa_wire_1692_straight : straight_statements rfa_wire_1692_mid.
Proof. vm_compute. exact I. Qed.
Lemma rfa_wire_1692_mid_safe : formal_typed_suffix_safe flat_memories 1692 rfa_wire_1692_mid.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma rfa_wire_1692_tail_safe : formal_typed_suffix_safe flat_memories 1692 rfa_wire_1692_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma rfa_wire_1692_nonreg : has_register 1692 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem rfa_reset_step_1692 inputs path old current result :
 VM.find 1502 old = Some (Gval (Fuint 32) (rfa_reset_word_20 inputs path)) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 VM.find 1692 result = Some (Gval (Fuint 32) (rfa_reset_word_20 inputs path)).
Proof.
 intros Source Step.
 apply (declared_connection_value 1771 flat_statements rfa_wire_1692_decl rfa_wire_1692_mid rfa_wire_1692_tail 1692 1502 32
 (Gval (Fuint 32) (rfa_reset_word_20 inputs path)) (Gval (Fuint 32) (rfa_reset_word_20 inputs path))
 (formal_invalid_policy inputs path) flat_memories old current result rfa_wire_1692_position rfa_wire_1692_split rfa_wire_1692_straight rfa_wire_1692_mid_safe rfa_wire_1692_tail_safe rfa_wire_1692_nonreg (Logic.eq_refl _) Source).
 - assert (Take : take 32 (rfa_reset_word_20 inputs path) = rfa_reset_word_20 inputs path).
   { apply take_oversize. rewrite rfa_reset_word_20_size. reflexivity. }
   cbn [adapt_hvalue_as_type]. rewrite Take. unfold zext_to,zext. rewrite rfa_reset_word_20_size subnn cats0. reflexivity.
 - exact Step.
Qed.
Theorem rfa_reset_history_1692 inputs path history limit :
 (forall t, (t < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history t) false (history t) flat_statements = Some (history (S t))) ->
 forall t, (4 <= t)%coq_nat -> (t <= limit)%coq_nat ->
 VM.find 1692 (history t) = Some (Gval (Fuint 32) (rfa_reset_word_20 inputs path)).
Proof.
 intros Steps t Lower Upper. destruct t as [|t]; [lia|].
 apply (rfa_reset_step_1692 inputs path (history t) (history t) (history (S t))).
 - apply (rfa_reset_history_1502 inputs path history limit Steps t);lia.
 - apply Steps;lia.
Qed.
Definition rfa_node_7409_expr := (@Eref VarOrder.T (@Eid VarOrder.T 1692)).
Definition rfa_node_7409_tail := match straight_drop 7581 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma rfa_node_7409_position : straight_drop 7580 flat_statements = Some (@Qcons VarOrder.T (@Snode VarOrder.T 7409 rfa_node_7409_expr) rfa_node_7409_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma rfa_node_7409_safe : formal_typed_suffix_safe flat_memories 7409 rfa_node_7409_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma rfa_node_7409_nonreg : has_register 7409 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem rfa_reset_step_7409 inputs path old current result :
 VM.find 1692 old = Some (Gval (Fuint 32) (rfa_reset_word_20 inputs path)) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 VM.find 7409 result = Some (Gval (Fuint 32) (rfa_reset_word_20 inputs path)).
Proof.
 intros Source Step.
 eapply formal_combinational_known_node;
 [exact rfa_node_7409_position|exact rfa_node_7409_safe|exact rfa_node_7409_nonreg| |reflexivity|exact Step].
 cbn [rfa_node_7409_expr eval_hfexpr_validif_policy eval_href_validif_policy]. exact Source.
Qed.
Theorem rfa_reset_history_7409 inputs path history limit :
 (forall t, (t < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history t) false (history t) flat_statements = Some (history (S t))) ->
 forall t, (5 <= t)%coq_nat -> (t <= limit)%coq_nat ->
 VM.find 7409 (history t) = Some (Gval (Fuint 32) (rfa_reset_word_20 inputs path)).
Proof.
 intros Steps t Lower Upper. destruct t as [|t]; [lia|].
 apply (rfa_reset_step_7409 inputs path (history t) (history t) (history (S t))).
 - apply (rfa_reset_history_1692 inputs path history limit Steps t);lia.
 - apply Steps;lia.
Qed.
Definition rfa_node_7410_expr := (@Eref VarOrder.T (@Eid VarOrder.T 7409)).
Definition rfa_node_7410_tail := match straight_drop 7582 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma rfa_node_7410_position : straight_drop 7581 flat_statements = Some (@Qcons VarOrder.T (@Snode VarOrder.T 7410 rfa_node_7410_expr) rfa_node_7410_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma rfa_node_7410_safe : formal_typed_suffix_safe flat_memories 7410 rfa_node_7410_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma rfa_node_7410_nonreg : has_register 7410 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem rfa_reset_step_7410 inputs path old current result :
 VM.find 7409 old = Some (Gval (Fuint 32) (rfa_reset_word_20 inputs path)) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 VM.find 7410 result = Some (Gval (Fuint 32) (rfa_reset_word_20 inputs path)).
Proof.
 intros Source Step.
 eapply formal_combinational_known_node;
 [exact rfa_node_7410_position|exact rfa_node_7410_safe|exact rfa_node_7410_nonreg| |reflexivity|exact Step].
 cbn [rfa_node_7410_expr eval_hfexpr_validif_policy eval_href_validif_policy]. exact Source.
Qed.
Theorem rfa_reset_history_7410 inputs path history limit :
 (forall t, (t < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history t) false (history t) flat_statements = Some (history (S t))) ->
 forall t, (6 <= t)%coq_nat -> (t <= limit)%coq_nat ->
 VM.find 7410 (history t) = Some (Gval (Fuint 32) (rfa_reset_word_20 inputs path)).
Proof.
 intros Steps t Lower Upper. destruct t as [|t]; [lia|].
 apply (rfa_reset_step_7410 inputs path (history t) (history t) (history (S t))).
 - apply (rfa_reset_history_7409 inputs path history limit Steps t);lia.
 - apply Steps;lia.
Qed.
Definition rfa_reset_word_21 inputs path := proj1_sig (formal_symbolic_inputs inputs path (validif_source_address (validif_raw_address nil 8637 0 nil)) nil 32).
Lemma rfa_reset_word_21_size inputs path : size (rfa_reset_word_21 inputs path) = 32%nat.
Proof. exact (proj2_sig (formal_symbolic_inputs inputs path (validif_source_address (validif_raw_address nil 8637 0 nil)) nil 32)). Qed.
Definition rfa_node_8131_expr := (@Evalidif VarOrder.T (@Econst VarOrder.T (Fuint 1) [::false]) (@Econst VarOrder.T (Fuint 32) [::false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false])).
Definition rfa_node_8131_tail := match straight_drop 8638 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma rfa_node_8131_position : straight_drop 8637 flat_statements = Some (@Qcons VarOrder.T (@Snode VarOrder.T 8131 rfa_node_8131_expr) rfa_node_8131_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma rfa_node_8131_safe : formal_typed_suffix_safe flat_memories 8131 rfa_node_8131_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma rfa_node_8131_nonreg : has_register 8131 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem rfa_reset_step_8131 inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 VM.find 8131 result = Some (Gval (Fuint 32) (rfa_reset_word_21 inputs path)).
Proof.
 intros Step.
 eapply formal_combinational_known_node;
 [exact rfa_node_8131_position|exact rfa_node_8131_safe|exact rfa_node_8131_nonreg| |reflexivity|exact Step].
 reflexivity.
Qed.
Theorem rfa_reset_history_8131 inputs path history limit :
 (forall t, (t < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history t) false (history t) flat_statements = Some (history (S t))) ->
 forall t, (1 <= t)%coq_nat -> (t <= limit)%coq_nat ->
 VM.find 8131 (history t) = Some (Gval (Fuint 32) (rfa_reset_word_21 inputs path)).
Proof.
 intros Steps t Lower Upper. destruct t as [|t]; [lia|].
 apply (rfa_reset_step_8131 inputs path (history t) (history t) (history (S t))).
 apply Steps;lia.
Qed.
Definition rfa_node_8132_expr := joint_update_expr_8132.
Theorem rfa_reset_step_8132 inputs path old current result :
 VM.find 8131 old = Some (Gval (Fuint 32) (rfa_reset_word_21 inputs path)) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 VM.find 8132 result = Some (Gval (Fuint 32) (rfa_reset_word_21 inputs path)).
Proof.
 intros Source Step.
 assert (Member : List.In (8132,joint_update_expr_8132) joint_update_expected_nodes).
 { apply (List.nth_error_In joint_update_expected_nodes 1019%nat). vm_compute. reflexivity. }
 destruct (selected_node_safe_position flat_memories flat_statements joint_update_node_offsets flat_statements joint_update_expected_nodes 8132 joint_update_expr_8132 joint_update_node_positions joint_update_node_safety Member) as [count [tail [Position [Safe Nonreg]]]].
 eapply formal_combinational_known_node; [exact Position|exact Safe|exact Nonreg| |reflexivity|exact Step].
 cbn [rfa_node_8132_expr eval_hfexpr_validif_policy eval_href_validif_policy]. exact Source.
Qed.
Theorem rfa_reset_history_8132 inputs path history limit :
 (forall t, (t < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history t) false (history t) flat_statements = Some (history (S t))) ->
 forall t, (2 <= t)%coq_nat -> (t <= limit)%coq_nat ->
 VM.find 8132 (history t) = Some (Gval (Fuint 32) (rfa_reset_word_21 inputs path)).
Proof.
 intros Steps t Lower Upper. destruct t as [|t]; [lia|].
 apply (rfa_reset_step_8132 inputs path (history t) (history t) (history (S t))).
 - apply (rfa_reset_history_8131 inputs path history limit Steps t);lia.
 - apply Steps;lia.
Qed.
Lemma joint_update_connection_808_nonreg : has_register 808 flat_statements = false.
Proof. exact joint_update_connection_808_nonregister. Qed.
Theorem rfa_reset_step_808 inputs path old current result :
 VM.find 8132 old = Some (Gval (Fuint 32) (rfa_reset_word_21 inputs path)) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 VM.find 808 result = Some (Gval (Fuint 32) (rfa_reset_word_21 inputs path)).
Proof.
 intros Source Step.
 apply (declared_connection_value 817 flat_statements joint_update_connection_808_decl joint_update_connection_808_mid joint_update_connection_808_tail 808 8132 32
 (Gval (Fuint 32) (rfa_reset_word_21 inputs path)) (Gval (Fuint 32) (rfa_reset_word_21 inputs path))
 (formal_invalid_policy inputs path) flat_memories old current result joint_update_connection_808_position joint_update_connection_808_split joint_update_connection_808_straight joint_update_connection_808_mid_safe joint_update_connection_808_tail_safe joint_update_connection_808_nonreg (Logic.eq_refl _) Source).
 - assert (Take : take 32 (rfa_reset_word_21 inputs path) = rfa_reset_word_21 inputs path).
   { apply take_oversize. rewrite rfa_reset_word_21_size. reflexivity. }
   cbn [adapt_hvalue_as_type]. rewrite Take. unfold zext_to,zext. rewrite rfa_reset_word_21_size subnn cats0. reflexivity.
 - exact Step.
Qed.
Theorem rfa_reset_history_808 inputs path history limit :
 (forall t, (t < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history t) false (history t) flat_statements = Some (history (S t))) ->
 forall t, (3 <= t)%coq_nat -> (t <= limit)%coq_nat ->
 VM.find 808 (history t) = Some (Gval (Fuint 32) (rfa_reset_word_21 inputs path)).
Proof.
 intros Steps t Lower Upper. destruct t as [|t]; [lia|].
 apply (rfa_reset_step_808 inputs path (history t) (history t) (history (S t))).
 - apply (rfa_reset_history_8132 inputs path history limit Steps t);lia.
 - apply Steps;lia.
Qed.
Definition rfa_node_1106_expr := joint_update_expr_1106.
Theorem rfa_reset_step_1106 inputs path old current result :
 VM.find 808 old = Some (Gval (Fuint 32) (rfa_reset_word_21 inputs path)) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 VM.find 1106 result = Some (Gval (Fuint 32) (rfa_reset_word_21 inputs path)).
Proof.
 intros Source Step.
 assert (Member : List.In (1106,joint_update_expr_1106) joint_update_expected_nodes).
 { apply (List.nth_error_In joint_update_expected_nodes 696%nat). vm_compute. reflexivity. }
 destruct (selected_node_safe_position flat_memories flat_statements joint_update_node_offsets flat_statements joint_update_expected_nodes 1106 joint_update_expr_1106 joint_update_node_positions joint_update_node_safety Member) as [count [tail [Position [Safe Nonreg]]]].
 eapply formal_combinational_known_node; [exact Position|exact Safe|exact Nonreg| |reflexivity|exact Step].
 cbn [rfa_node_1106_expr eval_hfexpr_validif_policy eval_href_validif_policy]. exact Source.
Qed.
Theorem rfa_reset_history_1106 inputs path history limit :
 (forall t, (t < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history t) false (history t) flat_statements = Some (history (S t))) ->
 forall t, (4 <= t)%coq_nat -> (t <= limit)%coq_nat ->
 VM.find 1106 (history t) = Some (Gval (Fuint 32) (rfa_reset_word_21 inputs path)).
Proof.
 intros Steps t Lower Upper. destruct t as [|t]; [lia|].
 apply (rfa_reset_step_1106 inputs path (history t) (history t) (history (S t))).
 - apply (rfa_reset_history_808 inputs path history limit Steps t);lia.
 - apply Steps;lia.
Qed.
Definition rfa_wire_1503_decl := match straight_drop 1583 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition rfa_wire_1503_tail := match straight_drop 8992 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition rfa_wire_1503_mid := take_statements 7408 rfa_wire_1503_decl.
Lemma rfa_wire_1503_position : straight_drop 1582 flat_statements = Some (@Qcons VarOrder.T (@Swire VarOrder.T 1503 (Gtyp (Fuint 32))) rfa_wire_1503_decl).
Proof. vm_compute. reflexivity. Qed.
Lemma rfa_wire_1503_split : rfa_wire_1503_decl = statement_append rfa_wire_1503_mid (@Qcons VarOrder.T (@Sfcnct VarOrder.T (@Eid VarOrder.T 1503) (@Eref VarOrder.T (@Eid VarOrder.T 8132))) rfa_wire_1503_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma rfa_wire_1503_straight : straight_statements rfa_wire_1503_mid.
Proof. vm_compute. exact I. Qed.
Lemma rfa_wire_1503_mid_safe : formal_typed_suffix_safe flat_memories 1503 rfa_wire_1503_mid.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma rfa_wire_1503_tail_safe : formal_typed_suffix_safe flat_memories 1503 rfa_wire_1503_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma rfa_wire_1503_nonreg : has_register 1503 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem rfa_reset_step_1503 inputs path old current result :
 VM.find 8132 old = Some (Gval (Fuint 32) (rfa_reset_word_21 inputs path)) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 VM.find 1503 result = Some (Gval (Fuint 32) (rfa_reset_word_21 inputs path)).
Proof.
 intros Source Step.
 apply (declared_connection_value 1582 flat_statements rfa_wire_1503_decl rfa_wire_1503_mid rfa_wire_1503_tail 1503 8132 32
 (Gval (Fuint 32) (rfa_reset_word_21 inputs path)) (Gval (Fuint 32) (rfa_reset_word_21 inputs path))
 (formal_invalid_policy inputs path) flat_memories old current result rfa_wire_1503_position rfa_wire_1503_split rfa_wire_1503_straight rfa_wire_1503_mid_safe rfa_wire_1503_tail_safe rfa_wire_1503_nonreg (Logic.eq_refl _) Source).
 - assert (Take : take 32 (rfa_reset_word_21 inputs path) = rfa_reset_word_21 inputs path).
   { apply take_oversize. rewrite rfa_reset_word_21_size. reflexivity. }
   cbn [adapt_hvalue_as_type]. rewrite Take. unfold zext_to,zext. rewrite rfa_reset_word_21_size subnn cats0. reflexivity.
 - exact Step.
Qed.
Theorem rfa_reset_history_1503 inputs path history limit :
 (forall t, (t < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history t) false (history t) flat_statements = Some (history (S t))) ->
 forall t, (3 <= t)%coq_nat -> (t <= limit)%coq_nat ->
 VM.find 1503 (history t) = Some (Gval (Fuint 32) (rfa_reset_word_21 inputs path)).
Proof.
 intros Steps t Lower Upper. destruct t as [|t]; [lia|].
 apply (rfa_reset_step_1503 inputs path (history t) (history t) (history (S t))).
 - apply (rfa_reset_history_8132 inputs path history limit Steps t);lia.
 - apply Steps;lia.
Qed.
Definition rfa_wire_1693_decl := match straight_drop 1773 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition rfa_wire_1693_tail := match straight_drop 8244 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition rfa_wire_1693_mid := take_statements 6470 rfa_wire_1693_decl.
Lemma rfa_wire_1693_position : straight_drop 1772 flat_statements = Some (@Qcons VarOrder.T (@Swire VarOrder.T 1693 (Gtyp (Fuint 32))) rfa_wire_1693_decl).
Proof. vm_compute. reflexivity. Qed.
Lemma rfa_wire_1693_split : rfa_wire_1693_decl = statement_append rfa_wire_1693_mid (@Qcons VarOrder.T (@Sfcnct VarOrder.T (@Eid VarOrder.T 1693) (@Eref VarOrder.T (@Eid VarOrder.T 1503))) rfa_wire_1693_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma rfa_wire_1693_straight : straight_statements rfa_wire_1693_mid.
Proof. vm_compute. exact I. Qed.
Lemma rfa_wire_1693_mid_safe : formal_typed_suffix_safe flat_memories 1693 rfa_wire_1693_mid.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma rfa_wire_1693_tail_safe : formal_typed_suffix_safe flat_memories 1693 rfa_wire_1693_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma rfa_wire_1693_nonreg : has_register 1693 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem rfa_reset_step_1693 inputs path old current result :
 VM.find 1503 old = Some (Gval (Fuint 32) (rfa_reset_word_21 inputs path)) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 VM.find 1693 result = Some (Gval (Fuint 32) (rfa_reset_word_21 inputs path)).
Proof.
 intros Source Step.
 apply (declared_connection_value 1772 flat_statements rfa_wire_1693_decl rfa_wire_1693_mid rfa_wire_1693_tail 1693 1503 32
 (Gval (Fuint 32) (rfa_reset_word_21 inputs path)) (Gval (Fuint 32) (rfa_reset_word_21 inputs path))
 (formal_invalid_policy inputs path) flat_memories old current result rfa_wire_1693_position rfa_wire_1693_split rfa_wire_1693_straight rfa_wire_1693_mid_safe rfa_wire_1693_tail_safe rfa_wire_1693_nonreg (Logic.eq_refl _) Source).
 - assert (Take : take 32 (rfa_reset_word_21 inputs path) = rfa_reset_word_21 inputs path).
   { apply take_oversize. rewrite rfa_reset_word_21_size. reflexivity. }
   cbn [adapt_hvalue_as_type]. rewrite Take. unfold zext_to,zext. rewrite rfa_reset_word_21_size subnn cats0. reflexivity.
 - exact Step.
Qed.
Theorem rfa_reset_history_1693 inputs path history limit :
 (forall t, (t < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history t) false (history t) flat_statements = Some (history (S t))) ->
 forall t, (4 <= t)%coq_nat -> (t <= limit)%coq_nat ->
 VM.find 1693 (history t) = Some (Gval (Fuint 32) (rfa_reset_word_21 inputs path)).
Proof.
 intros Steps t Lower Upper. destruct t as [|t]; [lia|].
 apply (rfa_reset_step_1693 inputs path (history t) (history t) (history (S t))).
 - apply (rfa_reset_history_1503 inputs path history limit Steps t);lia.
 - apply Steps;lia.
Qed.
Definition rfa_node_7411_expr := (@Eref VarOrder.T (@Eid VarOrder.T 1693)).
Definition rfa_node_7411_tail := match straight_drop 7583 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma rfa_node_7411_position : straight_drop 7582 flat_statements = Some (@Qcons VarOrder.T (@Snode VarOrder.T 7411 rfa_node_7411_expr) rfa_node_7411_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma rfa_node_7411_safe : formal_typed_suffix_safe flat_memories 7411 rfa_node_7411_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma rfa_node_7411_nonreg : has_register 7411 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem rfa_reset_step_7411 inputs path old current result :
 VM.find 1693 old = Some (Gval (Fuint 32) (rfa_reset_word_21 inputs path)) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 VM.find 7411 result = Some (Gval (Fuint 32) (rfa_reset_word_21 inputs path)).
Proof.
 intros Source Step.
 eapply formal_combinational_known_node;
 [exact rfa_node_7411_position|exact rfa_node_7411_safe|exact rfa_node_7411_nonreg| |reflexivity|exact Step].
 cbn [rfa_node_7411_expr eval_hfexpr_validif_policy eval_href_validif_policy]. exact Source.
Qed.
Theorem rfa_reset_history_7411 inputs path history limit :
 (forall t, (t < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history t) false (history t) flat_statements = Some (history (S t))) ->
 forall t, (5 <= t)%coq_nat -> (t <= limit)%coq_nat ->
 VM.find 7411 (history t) = Some (Gval (Fuint 32) (rfa_reset_word_21 inputs path)).
Proof.
 intros Steps t Lower Upper. destruct t as [|t]; [lia|].
 apply (rfa_reset_step_7411 inputs path (history t) (history t) (history (S t))).
 - apply (rfa_reset_history_1693 inputs path history limit Steps t);lia.
 - apply Steps;lia.
Qed.
Definition rfa_node_7412_expr := (@Eref VarOrder.T (@Eid VarOrder.T 7411)).
Definition rfa_node_7412_tail := match straight_drop 7584 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma rfa_node_7412_position : straight_drop 7583 flat_statements = Some (@Qcons VarOrder.T (@Snode VarOrder.T 7412 rfa_node_7412_expr) rfa_node_7412_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma rfa_node_7412_safe : formal_typed_suffix_safe flat_memories 7412 rfa_node_7412_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma rfa_node_7412_nonreg : has_register 7412 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem rfa_reset_step_7412 inputs path old current result :
 VM.find 7411 old = Some (Gval (Fuint 32) (rfa_reset_word_21 inputs path)) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 VM.find 7412 result = Some (Gval (Fuint 32) (rfa_reset_word_21 inputs path)).
Proof.
 intros Source Step.
 eapply formal_combinational_known_node;
 [exact rfa_node_7412_position|exact rfa_node_7412_safe|exact rfa_node_7412_nonreg| |reflexivity|exact Step].
 cbn [rfa_node_7412_expr eval_hfexpr_validif_policy eval_href_validif_policy]. exact Source.
Qed.
Theorem rfa_reset_history_7412 inputs path history limit :
 (forall t, (t < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history t) false (history t) flat_statements = Some (history (S t))) ->
 forall t, (6 <= t)%coq_nat -> (t <= limit)%coq_nat ->
 VM.find 7412 (history t) = Some (Gval (Fuint 32) (rfa_reset_word_21 inputs path)).
Proof.
 intros Steps t Lower Upper. destruct t as [|t]; [lia|].
 apply (rfa_reset_step_7412 inputs path (history t) (history t) (history (S t))).
 - apply (rfa_reset_history_7411 inputs path history limit Steps t);lia.
 - apply Steps;lia.
Qed.
Definition rfa_reset_word_22 inputs path := proj1_sig (formal_symbolic_inputs inputs path (validif_source_address (validif_raw_address nil 8639 0 nil)) nil 32).
Lemma rfa_reset_word_22_size inputs path : size (rfa_reset_word_22 inputs path) = 32%nat.
Proof. exact (proj2_sig (formal_symbolic_inputs inputs path (validif_source_address (validif_raw_address nil 8639 0 nil)) nil 32)). Qed.
Definition rfa_node_8133_expr := (@Evalidif VarOrder.T (@Econst VarOrder.T (Fuint 1) [::false]) (@Econst VarOrder.T (Fuint 32) [::false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false])).
Definition rfa_node_8133_tail := match straight_drop 8640 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma rfa_node_8133_position : straight_drop 8639 flat_statements = Some (@Qcons VarOrder.T (@Snode VarOrder.T 8133 rfa_node_8133_expr) rfa_node_8133_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma rfa_node_8133_safe : formal_typed_suffix_safe flat_memories 8133 rfa_node_8133_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma rfa_node_8133_nonreg : has_register 8133 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem rfa_reset_step_8133 inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 VM.find 8133 result = Some (Gval (Fuint 32) (rfa_reset_word_22 inputs path)).
Proof.
 intros Step.
 eapply formal_combinational_known_node;
 [exact rfa_node_8133_position|exact rfa_node_8133_safe|exact rfa_node_8133_nonreg| |reflexivity|exact Step].
 reflexivity.
Qed.
Theorem rfa_reset_history_8133 inputs path history limit :
 (forall t, (t < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history t) false (history t) flat_statements = Some (history (S t))) ->
 forall t, (1 <= t)%coq_nat -> (t <= limit)%coq_nat ->
 VM.find 8133 (history t) = Some (Gval (Fuint 32) (rfa_reset_word_22 inputs path)).
Proof.
 intros Steps t Lower Upper. destruct t as [|t]; [lia|].
 apply (rfa_reset_step_8133 inputs path (history t) (history t) (history (S t))).
 apply Steps;lia.
Qed.
Definition rfa_node_8134_expr := joint_update_expr_8134.
Theorem rfa_reset_step_8134 inputs path old current result :
 VM.find 8133 old = Some (Gval (Fuint 32) (rfa_reset_word_22 inputs path)) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 VM.find 8134 result = Some (Gval (Fuint 32) (rfa_reset_word_22 inputs path)).
Proof.
 intros Source Step.
 assert (Member : List.In (8134,joint_update_expr_8134) joint_update_expected_nodes).
 { apply (List.nth_error_In joint_update_expected_nodes 1021%nat). vm_compute. reflexivity. }
 destruct (selected_node_safe_position flat_memories flat_statements joint_update_node_offsets flat_statements joint_update_expected_nodes 8134 joint_update_expr_8134 joint_update_node_positions joint_update_node_safety Member) as [count [tail [Position [Safe Nonreg]]]].
 eapply formal_combinational_known_node; [exact Position|exact Safe|exact Nonreg| |reflexivity|exact Step].
 cbn [rfa_node_8134_expr eval_hfexpr_validif_policy eval_href_validif_policy]. exact Source.
Qed.
Theorem rfa_reset_history_8134 inputs path history limit :
 (forall t, (t < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history t) false (history t) flat_statements = Some (history (S t))) ->
 forall t, (2 <= t)%coq_nat -> (t <= limit)%coq_nat ->
 VM.find 8134 (history t) = Some (Gval (Fuint 32) (rfa_reset_word_22 inputs path)).
Proof.
 intros Steps t Lower Upper. destruct t as [|t]; [lia|].
 apply (rfa_reset_step_8134 inputs path (history t) (history t) (history (S t))).
 - apply (rfa_reset_history_8133 inputs path history limit Steps t);lia.
 - apply Steps;lia.
Qed.
Lemma joint_update_connection_809_nonreg : has_register 809 flat_statements = false.
Proof. exact joint_update_connection_809_nonregister. Qed.
Theorem rfa_reset_step_809 inputs path old current result :
 VM.find 8134 old = Some (Gval (Fuint 32) (rfa_reset_word_22 inputs path)) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 VM.find 809 result = Some (Gval (Fuint 32) (rfa_reset_word_22 inputs path)).
Proof.
 intros Source Step.
 apply (declared_connection_value 818 flat_statements joint_update_connection_809_decl joint_update_connection_809_mid joint_update_connection_809_tail 809 8134 32
 (Gval (Fuint 32) (rfa_reset_word_22 inputs path)) (Gval (Fuint 32) (rfa_reset_word_22 inputs path))
 (formal_invalid_policy inputs path) flat_memories old current result joint_update_connection_809_position joint_update_connection_809_split joint_update_connection_809_straight joint_update_connection_809_mid_safe joint_update_connection_809_tail_safe joint_update_connection_809_nonreg (Logic.eq_refl _) Source).
 - assert (Take : take 32 (rfa_reset_word_22 inputs path) = rfa_reset_word_22 inputs path).
   { apply take_oversize. rewrite rfa_reset_word_22_size. reflexivity. }
   cbn [adapt_hvalue_as_type]. rewrite Take. unfold zext_to,zext. rewrite rfa_reset_word_22_size subnn cats0. reflexivity.
 - exact Step.
Qed.
Theorem rfa_reset_history_809 inputs path history limit :
 (forall t, (t < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history t) false (history t) flat_statements = Some (history (S t))) ->
 forall t, (3 <= t)%coq_nat -> (t <= limit)%coq_nat ->
 VM.find 809 (history t) = Some (Gval (Fuint 32) (rfa_reset_word_22 inputs path)).
Proof.
 intros Steps t Lower Upper. destruct t as [|t]; [lia|].
 apply (rfa_reset_step_809 inputs path (history t) (history t) (history (S t))).
 - apply (rfa_reset_history_8134 inputs path history limit Steps t);lia.
 - apply Steps;lia.
Qed.
Definition rfa_node_1107_expr := joint_update_expr_1107.
Theorem rfa_reset_step_1107 inputs path old current result :
 VM.find 809 old = Some (Gval (Fuint 32) (rfa_reset_word_22 inputs path)) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 VM.find 1107 result = Some (Gval (Fuint 32) (rfa_reset_word_22 inputs path)).
Proof.
 intros Source Step.
 assert (Member : List.In (1107,joint_update_expr_1107) joint_update_expected_nodes).
 { apply (List.nth_error_In joint_update_expected_nodes 697%nat). vm_compute. reflexivity. }
 destruct (selected_node_safe_position flat_memories flat_statements joint_update_node_offsets flat_statements joint_update_expected_nodes 1107 joint_update_expr_1107 joint_update_node_positions joint_update_node_safety Member) as [count [tail [Position [Safe Nonreg]]]].
 eapply formal_combinational_known_node; [exact Position|exact Safe|exact Nonreg| |reflexivity|exact Step].
 cbn [rfa_node_1107_expr eval_hfexpr_validif_policy eval_href_validif_policy]. exact Source.
Qed.
Theorem rfa_reset_history_1107 inputs path history limit :
 (forall t, (t < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history t) false (history t) flat_statements = Some (history (S t))) ->
 forall t, (4 <= t)%coq_nat -> (t <= limit)%coq_nat ->
 VM.find 1107 (history t) = Some (Gval (Fuint 32) (rfa_reset_word_22 inputs path)).
Proof.
 intros Steps t Lower Upper. destruct t as [|t]; [lia|].
 apply (rfa_reset_step_1107 inputs path (history t) (history t) (history (S t))).
 - apply (rfa_reset_history_809 inputs path history limit Steps t);lia.
 - apply Steps;lia.
Qed.
Definition rfa_wire_1504_decl := match straight_drop 1584 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition rfa_wire_1504_tail := match straight_drop 8993 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition rfa_wire_1504_mid := take_statements 7408 rfa_wire_1504_decl.
Lemma rfa_wire_1504_position : straight_drop 1583 flat_statements = Some (@Qcons VarOrder.T (@Swire VarOrder.T 1504 (Gtyp (Fuint 32))) rfa_wire_1504_decl).
Proof. vm_compute. reflexivity. Qed.
Lemma rfa_wire_1504_split : rfa_wire_1504_decl = statement_append rfa_wire_1504_mid (@Qcons VarOrder.T (@Sfcnct VarOrder.T (@Eid VarOrder.T 1504) (@Eref VarOrder.T (@Eid VarOrder.T 8134))) rfa_wire_1504_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma rfa_wire_1504_straight : straight_statements rfa_wire_1504_mid.
Proof. vm_compute. exact I. Qed.
Lemma rfa_wire_1504_mid_safe : formal_typed_suffix_safe flat_memories 1504 rfa_wire_1504_mid.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma rfa_wire_1504_tail_safe : formal_typed_suffix_safe flat_memories 1504 rfa_wire_1504_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma rfa_wire_1504_nonreg : has_register 1504 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem rfa_reset_step_1504 inputs path old current result :
 VM.find 8134 old = Some (Gval (Fuint 32) (rfa_reset_word_22 inputs path)) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 VM.find 1504 result = Some (Gval (Fuint 32) (rfa_reset_word_22 inputs path)).
Proof.
 intros Source Step.
 apply (declared_connection_value 1583 flat_statements rfa_wire_1504_decl rfa_wire_1504_mid rfa_wire_1504_tail 1504 8134 32
 (Gval (Fuint 32) (rfa_reset_word_22 inputs path)) (Gval (Fuint 32) (rfa_reset_word_22 inputs path))
 (formal_invalid_policy inputs path) flat_memories old current result rfa_wire_1504_position rfa_wire_1504_split rfa_wire_1504_straight rfa_wire_1504_mid_safe rfa_wire_1504_tail_safe rfa_wire_1504_nonreg (Logic.eq_refl _) Source).
 - assert (Take : take 32 (rfa_reset_word_22 inputs path) = rfa_reset_word_22 inputs path).
   { apply take_oversize. rewrite rfa_reset_word_22_size. reflexivity. }
   cbn [adapt_hvalue_as_type]. rewrite Take. unfold zext_to,zext. rewrite rfa_reset_word_22_size subnn cats0. reflexivity.
 - exact Step.
Qed.
Theorem rfa_reset_history_1504 inputs path history limit :
 (forall t, (t < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history t) false (history t) flat_statements = Some (history (S t))) ->
 forall t, (3 <= t)%coq_nat -> (t <= limit)%coq_nat ->
 VM.find 1504 (history t) = Some (Gval (Fuint 32) (rfa_reset_word_22 inputs path)).
Proof.
 intros Steps t Lower Upper. destruct t as [|t]; [lia|].
 apply (rfa_reset_step_1504 inputs path (history t) (history t) (history (S t))).
 - apply (rfa_reset_history_8134 inputs path history limit Steps t);lia.
 - apply Steps;lia.
Qed.
Definition rfa_wire_1694_decl := match straight_drop 1774 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition rfa_wire_1694_tail := match straight_drop 8245 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition rfa_wire_1694_mid := take_statements 6470 rfa_wire_1694_decl.
Lemma rfa_wire_1694_position : straight_drop 1773 flat_statements = Some (@Qcons VarOrder.T (@Swire VarOrder.T 1694 (Gtyp (Fuint 32))) rfa_wire_1694_decl).
Proof. vm_compute. reflexivity. Qed.
Lemma rfa_wire_1694_split : rfa_wire_1694_decl = statement_append rfa_wire_1694_mid (@Qcons VarOrder.T (@Sfcnct VarOrder.T (@Eid VarOrder.T 1694) (@Eref VarOrder.T (@Eid VarOrder.T 1504))) rfa_wire_1694_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma rfa_wire_1694_straight : straight_statements rfa_wire_1694_mid.
Proof. vm_compute. exact I. Qed.
Lemma rfa_wire_1694_mid_safe : formal_typed_suffix_safe flat_memories 1694 rfa_wire_1694_mid.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma rfa_wire_1694_tail_safe : formal_typed_suffix_safe flat_memories 1694 rfa_wire_1694_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma rfa_wire_1694_nonreg : has_register 1694 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem rfa_reset_step_1694 inputs path old current result :
 VM.find 1504 old = Some (Gval (Fuint 32) (rfa_reset_word_22 inputs path)) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 VM.find 1694 result = Some (Gval (Fuint 32) (rfa_reset_word_22 inputs path)).
Proof.
 intros Source Step.
 apply (declared_connection_value 1773 flat_statements rfa_wire_1694_decl rfa_wire_1694_mid rfa_wire_1694_tail 1694 1504 32
 (Gval (Fuint 32) (rfa_reset_word_22 inputs path)) (Gval (Fuint 32) (rfa_reset_word_22 inputs path))
 (formal_invalid_policy inputs path) flat_memories old current result rfa_wire_1694_position rfa_wire_1694_split rfa_wire_1694_straight rfa_wire_1694_mid_safe rfa_wire_1694_tail_safe rfa_wire_1694_nonreg (Logic.eq_refl _) Source).
 - assert (Take : take 32 (rfa_reset_word_22 inputs path) = rfa_reset_word_22 inputs path).
   { apply take_oversize. rewrite rfa_reset_word_22_size. reflexivity. }
   cbn [adapt_hvalue_as_type]. rewrite Take. unfold zext_to,zext. rewrite rfa_reset_word_22_size subnn cats0. reflexivity.
 - exact Step.
Qed.
Theorem rfa_reset_history_1694 inputs path history limit :
 (forall t, (t < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history t) false (history t) flat_statements = Some (history (S t))) ->
 forall t, (4 <= t)%coq_nat -> (t <= limit)%coq_nat ->
 VM.find 1694 (history t) = Some (Gval (Fuint 32) (rfa_reset_word_22 inputs path)).
Proof.
 intros Steps t Lower Upper. destruct t as [|t]; [lia|].
 apply (rfa_reset_step_1694 inputs path (history t) (history t) (history (S t))).
 - apply (rfa_reset_history_1504 inputs path history limit Steps t);lia.
 - apply Steps;lia.
Qed.
Definition rfa_node_7413_expr := (@Eref VarOrder.T (@Eid VarOrder.T 1694)).
Definition rfa_node_7413_tail := match straight_drop 7585 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma rfa_node_7413_position : straight_drop 7584 flat_statements = Some (@Qcons VarOrder.T (@Snode VarOrder.T 7413 rfa_node_7413_expr) rfa_node_7413_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma rfa_node_7413_safe : formal_typed_suffix_safe flat_memories 7413 rfa_node_7413_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma rfa_node_7413_nonreg : has_register 7413 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem rfa_reset_step_7413 inputs path old current result :
 VM.find 1694 old = Some (Gval (Fuint 32) (rfa_reset_word_22 inputs path)) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 VM.find 7413 result = Some (Gval (Fuint 32) (rfa_reset_word_22 inputs path)).
Proof.
 intros Source Step.
 eapply formal_combinational_known_node;
 [exact rfa_node_7413_position|exact rfa_node_7413_safe|exact rfa_node_7413_nonreg| |reflexivity|exact Step].
 cbn [rfa_node_7413_expr eval_hfexpr_validif_policy eval_href_validif_policy]. exact Source.
Qed.
Theorem rfa_reset_history_7413 inputs path history limit :
 (forall t, (t < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history t) false (history t) flat_statements = Some (history (S t))) ->
 forall t, (5 <= t)%coq_nat -> (t <= limit)%coq_nat ->
 VM.find 7413 (history t) = Some (Gval (Fuint 32) (rfa_reset_word_22 inputs path)).
Proof.
 intros Steps t Lower Upper. destruct t as [|t]; [lia|].
 apply (rfa_reset_step_7413 inputs path (history t) (history t) (history (S t))).
 - apply (rfa_reset_history_1694 inputs path history limit Steps t);lia.
 - apply Steps;lia.
Qed.
Definition rfa_node_7414_expr := (@Eref VarOrder.T (@Eid VarOrder.T 7413)).
Definition rfa_node_7414_tail := match straight_drop 7586 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma rfa_node_7414_position : straight_drop 7585 flat_statements = Some (@Qcons VarOrder.T (@Snode VarOrder.T 7414 rfa_node_7414_expr) rfa_node_7414_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma rfa_node_7414_safe : formal_typed_suffix_safe flat_memories 7414 rfa_node_7414_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma rfa_node_7414_nonreg : has_register 7414 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem rfa_reset_step_7414 inputs path old current result :
 VM.find 7413 old = Some (Gval (Fuint 32) (rfa_reset_word_22 inputs path)) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 VM.find 7414 result = Some (Gval (Fuint 32) (rfa_reset_word_22 inputs path)).
Proof.
 intros Source Step.
 eapply formal_combinational_known_node;
 [exact rfa_node_7414_position|exact rfa_node_7414_safe|exact rfa_node_7414_nonreg| |reflexivity|exact Step].
 cbn [rfa_node_7414_expr eval_hfexpr_validif_policy eval_href_validif_policy]. exact Source.
Qed.
Theorem rfa_reset_history_7414 inputs path history limit :
 (forall t, (t < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history t) false (history t) flat_statements = Some (history (S t))) ->
 forall t, (6 <= t)%coq_nat -> (t <= limit)%coq_nat ->
 VM.find 7414 (history t) = Some (Gval (Fuint 32) (rfa_reset_word_22 inputs path)).
Proof.
 intros Steps t Lower Upper. destruct t as [|t]; [lia|].
 apply (rfa_reset_step_7414 inputs path (history t) (history t) (history (S t))).
 - apply (rfa_reset_history_7413 inputs path history limit Steps t);lia.
 - apply Steps;lia.
Qed.
Definition rfa_reset_word_23 inputs path := proj1_sig (formal_symbolic_inputs inputs path (validif_source_address (validif_raw_address nil 8641 0 nil)) nil 32).
Lemma rfa_reset_word_23_size inputs path : size (rfa_reset_word_23 inputs path) = 32%nat.
Proof. exact (proj2_sig (formal_symbolic_inputs inputs path (validif_source_address (validif_raw_address nil 8641 0 nil)) nil 32)). Qed.
Definition rfa_node_8135_expr := (@Evalidif VarOrder.T (@Econst VarOrder.T (Fuint 1) [::false]) (@Econst VarOrder.T (Fuint 32) [::false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false])).
Definition rfa_node_8135_tail := match straight_drop 8642 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma rfa_node_8135_position : straight_drop 8641 flat_statements = Some (@Qcons VarOrder.T (@Snode VarOrder.T 8135 rfa_node_8135_expr) rfa_node_8135_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma rfa_node_8135_safe : formal_typed_suffix_safe flat_memories 8135 rfa_node_8135_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma rfa_node_8135_nonreg : has_register 8135 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem rfa_reset_step_8135 inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 VM.find 8135 result = Some (Gval (Fuint 32) (rfa_reset_word_23 inputs path)).
Proof.
 intros Step.
 eapply formal_combinational_known_node;
 [exact rfa_node_8135_position|exact rfa_node_8135_safe|exact rfa_node_8135_nonreg| |reflexivity|exact Step].
 reflexivity.
Qed.
Theorem rfa_reset_history_8135 inputs path history limit :
 (forall t, (t < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history t) false (history t) flat_statements = Some (history (S t))) ->
 forall t, (1 <= t)%coq_nat -> (t <= limit)%coq_nat ->
 VM.find 8135 (history t) = Some (Gval (Fuint 32) (rfa_reset_word_23 inputs path)).
Proof.
 intros Steps t Lower Upper. destruct t as [|t]; [lia|].
 apply (rfa_reset_step_8135 inputs path (history t) (history t) (history (S t))).
 apply Steps;lia.
Qed.
Definition rfa_node_8136_expr := joint_update_expr_8136.
Theorem rfa_reset_step_8136 inputs path old current result :
 VM.find 8135 old = Some (Gval (Fuint 32) (rfa_reset_word_23 inputs path)) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 VM.find 8136 result = Some (Gval (Fuint 32) (rfa_reset_word_23 inputs path)).
Proof.
 intros Source Step.
 assert (Member : List.In (8136,joint_update_expr_8136) joint_update_expected_nodes).
 { apply (List.nth_error_In joint_update_expected_nodes 1023%nat). vm_compute. reflexivity. }
 destruct (selected_node_safe_position flat_memories flat_statements joint_update_node_offsets flat_statements joint_update_expected_nodes 8136 joint_update_expr_8136 joint_update_node_positions joint_update_node_safety Member) as [count [tail [Position [Safe Nonreg]]]].
 eapply formal_combinational_known_node; [exact Position|exact Safe|exact Nonreg| |reflexivity|exact Step].
 cbn [rfa_node_8136_expr eval_hfexpr_validif_policy eval_href_validif_policy]. exact Source.
Qed.
Theorem rfa_reset_history_8136 inputs path history limit :
 (forall t, (t < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history t) false (history t) flat_statements = Some (history (S t))) ->
 forall t, (2 <= t)%coq_nat -> (t <= limit)%coq_nat ->
 VM.find 8136 (history t) = Some (Gval (Fuint 32) (rfa_reset_word_23 inputs path)).
Proof.
 intros Steps t Lower Upper. destruct t as [|t]; [lia|].
 apply (rfa_reset_step_8136 inputs path (history t) (history t) (history (S t))).
 - apply (rfa_reset_history_8135 inputs path history limit Steps t);lia.
 - apply Steps;lia.
Qed.
Lemma joint_update_connection_810_nonreg : has_register 810 flat_statements = false.
Proof. exact joint_update_connection_810_nonregister. Qed.
Theorem rfa_reset_step_810 inputs path old current result :
 VM.find 8136 old = Some (Gval (Fuint 32) (rfa_reset_word_23 inputs path)) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 VM.find 810 result = Some (Gval (Fuint 32) (rfa_reset_word_23 inputs path)).
Proof.
 intros Source Step.
 apply (declared_connection_value 819 flat_statements joint_update_connection_810_decl joint_update_connection_810_mid joint_update_connection_810_tail 810 8136 32
 (Gval (Fuint 32) (rfa_reset_word_23 inputs path)) (Gval (Fuint 32) (rfa_reset_word_23 inputs path))
 (formal_invalid_policy inputs path) flat_memories old current result joint_update_connection_810_position joint_update_connection_810_split joint_update_connection_810_straight joint_update_connection_810_mid_safe joint_update_connection_810_tail_safe joint_update_connection_810_nonreg (Logic.eq_refl _) Source).
 - assert (Take : take 32 (rfa_reset_word_23 inputs path) = rfa_reset_word_23 inputs path).
   { apply take_oversize. rewrite rfa_reset_word_23_size. reflexivity. }
   cbn [adapt_hvalue_as_type]. rewrite Take. unfold zext_to,zext. rewrite rfa_reset_word_23_size subnn cats0. reflexivity.
 - exact Step.
Qed.
Theorem rfa_reset_history_810 inputs path history limit :
 (forall t, (t < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history t) false (history t) flat_statements = Some (history (S t))) ->
 forall t, (3 <= t)%coq_nat -> (t <= limit)%coq_nat ->
 VM.find 810 (history t) = Some (Gval (Fuint 32) (rfa_reset_word_23 inputs path)).
Proof.
 intros Steps t Lower Upper. destruct t as [|t]; [lia|].
 apply (rfa_reset_step_810 inputs path (history t) (history t) (history (S t))).
 - apply (rfa_reset_history_8136 inputs path history limit Steps t);lia.
 - apply Steps;lia.
Qed.
Definition rfa_node_1108_expr := joint_update_expr_1108.
Theorem rfa_reset_step_1108 inputs path old current result :
 VM.find 810 old = Some (Gval (Fuint 32) (rfa_reset_word_23 inputs path)) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 VM.find 1108 result = Some (Gval (Fuint 32) (rfa_reset_word_23 inputs path)).
Proof.
 intros Source Step.
 assert (Member : List.In (1108,joint_update_expr_1108) joint_update_expected_nodes).
 { apply (List.nth_error_In joint_update_expected_nodes 698%nat). vm_compute. reflexivity. }
 destruct (selected_node_safe_position flat_memories flat_statements joint_update_node_offsets flat_statements joint_update_expected_nodes 1108 joint_update_expr_1108 joint_update_node_positions joint_update_node_safety Member) as [count [tail [Position [Safe Nonreg]]]].
 eapply formal_combinational_known_node; [exact Position|exact Safe|exact Nonreg| |reflexivity|exact Step].
 cbn [rfa_node_1108_expr eval_hfexpr_validif_policy eval_href_validif_policy]. exact Source.
Qed.
Theorem rfa_reset_history_1108 inputs path history limit :
 (forall t, (t < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history t) false (history t) flat_statements = Some (history (S t))) ->
 forall t, (4 <= t)%coq_nat -> (t <= limit)%coq_nat ->
 VM.find 1108 (history t) = Some (Gval (Fuint 32) (rfa_reset_word_23 inputs path)).
Proof.
 intros Steps t Lower Upper. destruct t as [|t]; [lia|].
 apply (rfa_reset_step_1108 inputs path (history t) (history t) (history (S t))).
 - apply (rfa_reset_history_810 inputs path history limit Steps t);lia.
 - apply Steps;lia.
Qed.
Definition rfa_wire_1505_decl := match straight_drop 1585 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition rfa_wire_1505_tail := match straight_drop 8994 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition rfa_wire_1505_mid := take_statements 7408 rfa_wire_1505_decl.
Lemma rfa_wire_1505_position : straight_drop 1584 flat_statements = Some (@Qcons VarOrder.T (@Swire VarOrder.T 1505 (Gtyp (Fuint 32))) rfa_wire_1505_decl).
Proof. vm_compute. reflexivity. Qed.
Lemma rfa_wire_1505_split : rfa_wire_1505_decl = statement_append rfa_wire_1505_mid (@Qcons VarOrder.T (@Sfcnct VarOrder.T (@Eid VarOrder.T 1505) (@Eref VarOrder.T (@Eid VarOrder.T 8136))) rfa_wire_1505_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma rfa_wire_1505_straight : straight_statements rfa_wire_1505_mid.
Proof. vm_compute. exact I. Qed.
Lemma rfa_wire_1505_mid_safe : formal_typed_suffix_safe flat_memories 1505 rfa_wire_1505_mid.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma rfa_wire_1505_tail_safe : formal_typed_suffix_safe flat_memories 1505 rfa_wire_1505_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma rfa_wire_1505_nonreg : has_register 1505 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem rfa_reset_step_1505 inputs path old current result :
 VM.find 8136 old = Some (Gval (Fuint 32) (rfa_reset_word_23 inputs path)) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 VM.find 1505 result = Some (Gval (Fuint 32) (rfa_reset_word_23 inputs path)).
Proof.
 intros Source Step.
 apply (declared_connection_value 1584 flat_statements rfa_wire_1505_decl rfa_wire_1505_mid rfa_wire_1505_tail 1505 8136 32
 (Gval (Fuint 32) (rfa_reset_word_23 inputs path)) (Gval (Fuint 32) (rfa_reset_word_23 inputs path))
 (formal_invalid_policy inputs path) flat_memories old current result rfa_wire_1505_position rfa_wire_1505_split rfa_wire_1505_straight rfa_wire_1505_mid_safe rfa_wire_1505_tail_safe rfa_wire_1505_nonreg (Logic.eq_refl _) Source).
 - assert (Take : take 32 (rfa_reset_word_23 inputs path) = rfa_reset_word_23 inputs path).
   { apply take_oversize. rewrite rfa_reset_word_23_size. reflexivity. }
   cbn [adapt_hvalue_as_type]. rewrite Take. unfold zext_to,zext. rewrite rfa_reset_word_23_size subnn cats0. reflexivity.
 - exact Step.
Qed.
Theorem rfa_reset_history_1505 inputs path history limit :
 (forall t, (t < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history t) false (history t) flat_statements = Some (history (S t))) ->
 forall t, (3 <= t)%coq_nat -> (t <= limit)%coq_nat ->
 VM.find 1505 (history t) = Some (Gval (Fuint 32) (rfa_reset_word_23 inputs path)).
Proof.
 intros Steps t Lower Upper. destruct t as [|t]; [lia|].
 apply (rfa_reset_step_1505 inputs path (history t) (history t) (history (S t))).
 - apply (rfa_reset_history_8136 inputs path history limit Steps t);lia.
 - apply Steps;lia.
Qed.
Definition rfa_wire_1695_decl := match straight_drop 1775 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition rfa_wire_1695_tail := match straight_drop 8246 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition rfa_wire_1695_mid := take_statements 6470 rfa_wire_1695_decl.
Lemma rfa_wire_1695_position : straight_drop 1774 flat_statements = Some (@Qcons VarOrder.T (@Swire VarOrder.T 1695 (Gtyp (Fuint 32))) rfa_wire_1695_decl).
Proof. vm_compute. reflexivity. Qed.
Lemma rfa_wire_1695_split : rfa_wire_1695_decl = statement_append rfa_wire_1695_mid (@Qcons VarOrder.T (@Sfcnct VarOrder.T (@Eid VarOrder.T 1695) (@Eref VarOrder.T (@Eid VarOrder.T 1505))) rfa_wire_1695_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma rfa_wire_1695_straight : straight_statements rfa_wire_1695_mid.
Proof. vm_compute. exact I. Qed.
Lemma rfa_wire_1695_mid_safe : formal_typed_suffix_safe flat_memories 1695 rfa_wire_1695_mid.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma rfa_wire_1695_tail_safe : formal_typed_suffix_safe flat_memories 1695 rfa_wire_1695_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma rfa_wire_1695_nonreg : has_register 1695 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem rfa_reset_step_1695 inputs path old current result :
 VM.find 1505 old = Some (Gval (Fuint 32) (rfa_reset_word_23 inputs path)) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 VM.find 1695 result = Some (Gval (Fuint 32) (rfa_reset_word_23 inputs path)).
Proof.
 intros Source Step.
 apply (declared_connection_value 1774 flat_statements rfa_wire_1695_decl rfa_wire_1695_mid rfa_wire_1695_tail 1695 1505 32
 (Gval (Fuint 32) (rfa_reset_word_23 inputs path)) (Gval (Fuint 32) (rfa_reset_word_23 inputs path))
 (formal_invalid_policy inputs path) flat_memories old current result rfa_wire_1695_position rfa_wire_1695_split rfa_wire_1695_straight rfa_wire_1695_mid_safe rfa_wire_1695_tail_safe rfa_wire_1695_nonreg (Logic.eq_refl _) Source).
 - assert (Take : take 32 (rfa_reset_word_23 inputs path) = rfa_reset_word_23 inputs path).
   { apply take_oversize. rewrite rfa_reset_word_23_size. reflexivity. }
   cbn [adapt_hvalue_as_type]. rewrite Take. unfold zext_to,zext. rewrite rfa_reset_word_23_size subnn cats0. reflexivity.
 - exact Step.
Qed.
Theorem rfa_reset_history_1695 inputs path history limit :
 (forall t, (t < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history t) false (history t) flat_statements = Some (history (S t))) ->
 forall t, (4 <= t)%coq_nat -> (t <= limit)%coq_nat ->
 VM.find 1695 (history t) = Some (Gval (Fuint 32) (rfa_reset_word_23 inputs path)).
Proof.
 intros Steps t Lower Upper. destruct t as [|t]; [lia|].
 apply (rfa_reset_step_1695 inputs path (history t) (history t) (history (S t))).
 - apply (rfa_reset_history_1505 inputs path history limit Steps t);lia.
 - apply Steps;lia.
Qed.
Definition rfa_node_7415_expr := (@Eref VarOrder.T (@Eid VarOrder.T 1695)).
Definition rfa_node_7415_tail := match straight_drop 7587 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma rfa_node_7415_position : straight_drop 7586 flat_statements = Some (@Qcons VarOrder.T (@Snode VarOrder.T 7415 rfa_node_7415_expr) rfa_node_7415_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma rfa_node_7415_safe : formal_typed_suffix_safe flat_memories 7415 rfa_node_7415_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma rfa_node_7415_nonreg : has_register 7415 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem rfa_reset_step_7415 inputs path old current result :
 VM.find 1695 old = Some (Gval (Fuint 32) (rfa_reset_word_23 inputs path)) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 VM.find 7415 result = Some (Gval (Fuint 32) (rfa_reset_word_23 inputs path)).
Proof.
 intros Source Step.
 eapply formal_combinational_known_node;
 [exact rfa_node_7415_position|exact rfa_node_7415_safe|exact rfa_node_7415_nonreg| |reflexivity|exact Step].
 cbn [rfa_node_7415_expr eval_hfexpr_validif_policy eval_href_validif_policy]. exact Source.
Qed.
Theorem rfa_reset_history_7415 inputs path history limit :
 (forall t, (t < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history t) false (history t) flat_statements = Some (history (S t))) ->
 forall t, (5 <= t)%coq_nat -> (t <= limit)%coq_nat ->
 VM.find 7415 (history t) = Some (Gval (Fuint 32) (rfa_reset_word_23 inputs path)).
Proof.
 intros Steps t Lower Upper. destruct t as [|t]; [lia|].
 apply (rfa_reset_step_7415 inputs path (history t) (history t) (history (S t))).
 - apply (rfa_reset_history_1695 inputs path history limit Steps t);lia.
 - apply Steps;lia.
Qed.
Definition rfa_node_7416_expr := (@Eref VarOrder.T (@Eid VarOrder.T 7415)).
Definition rfa_node_7416_tail := match straight_drop 7588 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma rfa_node_7416_position : straight_drop 7587 flat_statements = Some (@Qcons VarOrder.T (@Snode VarOrder.T 7416 rfa_node_7416_expr) rfa_node_7416_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma rfa_node_7416_safe : formal_typed_suffix_safe flat_memories 7416 rfa_node_7416_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma rfa_node_7416_nonreg : has_register 7416 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem rfa_reset_step_7416 inputs path old current result :
 VM.find 7415 old = Some (Gval (Fuint 32) (rfa_reset_word_23 inputs path)) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 VM.find 7416 result = Some (Gval (Fuint 32) (rfa_reset_word_23 inputs path)).
Proof.
 intros Source Step.
 eapply formal_combinational_known_node;
 [exact rfa_node_7416_position|exact rfa_node_7416_safe|exact rfa_node_7416_nonreg| |reflexivity|exact Step].
 cbn [rfa_node_7416_expr eval_hfexpr_validif_policy eval_href_validif_policy]. exact Source.
Qed.
Theorem rfa_reset_history_7416 inputs path history limit :
 (forall t, (t < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history t) false (history t) flat_statements = Some (history (S t))) ->
 forall t, (6 <= t)%coq_nat -> (t <= limit)%coq_nat ->
 VM.find 7416 (history t) = Some (Gval (Fuint 32) (rfa_reset_word_23 inputs path)).
Proof.
 intros Steps t Lower Upper. destruct t as [|t]; [lia|].
 apply (rfa_reset_step_7416 inputs path (history t) (history t) (history (S t))).
 - apply (rfa_reset_history_7415 inputs path history limit Steps t);lia.
 - apply Steps;lia.
Qed.
