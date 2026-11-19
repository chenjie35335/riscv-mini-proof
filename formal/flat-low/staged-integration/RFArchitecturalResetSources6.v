Require Import SelectedNodeSafety JointUpdateNodePositions JointUpdateExpressionCertificates JointUpdateConnectionCertificates CoreSocModel ComparisonNodes ScalarNodeFrames FormalTypedNodeFrames RegisterInvariants FormalTypedNodeEquation FormalDeclaredConnection FormalStatementSegments RegisterCommitCertificate FormalUIntRegisterCommitSource SelectedUIntMuxIdentity UIntResizeRoundtrip.
From Coq Require Import ZArith List Lia.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From nbits Require Import NBits.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Definition rfa_reset_word_24 inputs path := proj1_sig (formal_symbolic_inputs inputs path (validif_source_address (validif_raw_address nil 8643 0 nil)) nil 32).
Lemma rfa_reset_word_24_size inputs path : size (rfa_reset_word_24 inputs path) = 32%nat.
Proof. exact (proj2_sig (formal_symbolic_inputs inputs path (validif_source_address (validif_raw_address nil 8643 0 nil)) nil 32)). Qed.
Definition rfa_node_8137_expr := (@Evalidif VarOrder.T (@Econst VarOrder.T (Fuint 1) [::false]) (@Econst VarOrder.T (Fuint 32) [::false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false])).
Definition rfa_node_8137_tail := match straight_drop 8644 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma rfa_node_8137_position : straight_drop 8643 flat_statements = Some (@Qcons VarOrder.T (@Snode VarOrder.T 8137 rfa_node_8137_expr) rfa_node_8137_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma rfa_node_8137_safe : formal_typed_suffix_safe flat_memories 8137 rfa_node_8137_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma rfa_node_8137_nonreg : has_register 8137 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem rfa_reset_step_8137 inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 VM.find 8137 result = Some (Gval (Fuint 32) (rfa_reset_word_24 inputs path)).
Proof.
 intros Step.
 eapply formal_combinational_known_node;
 [exact rfa_node_8137_position|exact rfa_node_8137_safe|exact rfa_node_8137_nonreg| |reflexivity|exact Step].
 reflexivity.
Qed.
Theorem rfa_reset_history_8137 inputs path history limit :
 (forall t, (t < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history t) false (history t) flat_statements = Some (history (S t))) ->
 forall t, (1 <= t)%coq_nat -> (t <= limit)%coq_nat ->
 VM.find 8137 (history t) = Some (Gval (Fuint 32) (rfa_reset_word_24 inputs path)).
Proof.
 intros Steps t Lower Upper. destruct t as [|t]; [lia|].
 apply (rfa_reset_step_8137 inputs path (history t) (history t) (history (S t))).
 apply Steps;lia.
Qed.
Definition rfa_node_8138_expr := joint_update_expr_8138.
Theorem rfa_reset_step_8138 inputs path old current result :
 VM.find 8137 old = Some (Gval (Fuint 32) (rfa_reset_word_24 inputs path)) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 VM.find 8138 result = Some (Gval (Fuint 32) (rfa_reset_word_24 inputs path)).
Proof.
 intros Source Step.
 assert (Member : List.In (8138,joint_update_expr_8138) joint_update_expected_nodes).
 { apply (List.nth_error_In joint_update_expected_nodes 1025%nat). vm_compute. reflexivity. }
 destruct (selected_node_safe_position flat_memories flat_statements joint_update_node_offsets flat_statements joint_update_expected_nodes 8138 joint_update_expr_8138 joint_update_node_positions joint_update_node_safety Member) as [count [tail [Position [Safe Nonreg]]]].
 eapply formal_combinational_known_node; [exact Position|exact Safe|exact Nonreg| |reflexivity|exact Step].
 cbn [rfa_node_8138_expr eval_hfexpr_validif_policy eval_href_validif_policy]. exact Source.
Qed.
Theorem rfa_reset_history_8138 inputs path history limit :
 (forall t, (t < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history t) false (history t) flat_statements = Some (history (S t))) ->
 forall t, (2 <= t)%coq_nat -> (t <= limit)%coq_nat ->
 VM.find 8138 (history t) = Some (Gval (Fuint 32) (rfa_reset_word_24 inputs path)).
Proof.
 intros Steps t Lower Upper. destruct t as [|t]; [lia|].
 apply (rfa_reset_step_8138 inputs path (history t) (history t) (history (S t))).
 - apply (rfa_reset_history_8137 inputs path history limit Steps t);lia.
 - apply Steps;lia.
Qed.
Lemma joint_update_connection_811_nonreg : has_register 811 flat_statements = false.
Proof. exact joint_update_connection_811_nonregister. Qed.
Theorem rfa_reset_step_811 inputs path old current result :
 VM.find 8138 old = Some (Gval (Fuint 32) (rfa_reset_word_24 inputs path)) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 VM.find 811 result = Some (Gval (Fuint 32) (rfa_reset_word_24 inputs path)).
Proof.
 intros Source Step.
 apply (declared_connection_value 820 flat_statements joint_update_connection_811_decl joint_update_connection_811_mid joint_update_connection_811_tail 811 8138 32
 (Gval (Fuint 32) (rfa_reset_word_24 inputs path)) (Gval (Fuint 32) (rfa_reset_word_24 inputs path))
 (formal_invalid_policy inputs path) flat_memories old current result joint_update_connection_811_position joint_update_connection_811_split joint_update_connection_811_straight joint_update_connection_811_mid_safe joint_update_connection_811_tail_safe joint_update_connection_811_nonreg (Logic.eq_refl _) Source).
 - assert (Take : take 32 (rfa_reset_word_24 inputs path) = rfa_reset_word_24 inputs path).
   { apply take_oversize. rewrite rfa_reset_word_24_size. reflexivity. }
   cbn [adapt_hvalue_as_type]. rewrite Take. unfold zext_to,zext. rewrite rfa_reset_word_24_size subnn cats0. reflexivity.
 - exact Step.
Qed.
Theorem rfa_reset_history_811 inputs path history limit :
 (forall t, (t < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history t) false (history t) flat_statements = Some (history (S t))) ->
 forall t, (3 <= t)%coq_nat -> (t <= limit)%coq_nat ->
 VM.find 811 (history t) = Some (Gval (Fuint 32) (rfa_reset_word_24 inputs path)).
Proof.
 intros Steps t Lower Upper. destruct t as [|t]; [lia|].
 apply (rfa_reset_step_811 inputs path (history t) (history t) (history (S t))).
 - apply (rfa_reset_history_8138 inputs path history limit Steps t);lia.
 - apply Steps;lia.
Qed.
Definition rfa_node_1109_expr := joint_update_expr_1109.
Theorem rfa_reset_step_1109 inputs path old current result :
 VM.find 811 old = Some (Gval (Fuint 32) (rfa_reset_word_24 inputs path)) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 VM.find 1109 result = Some (Gval (Fuint 32) (rfa_reset_word_24 inputs path)).
Proof.
 intros Source Step.
 assert (Member : List.In (1109,joint_update_expr_1109) joint_update_expected_nodes).
 { apply (List.nth_error_In joint_update_expected_nodes 699%nat). vm_compute. reflexivity. }
 destruct (selected_node_safe_position flat_memories flat_statements joint_update_node_offsets flat_statements joint_update_expected_nodes 1109 joint_update_expr_1109 joint_update_node_positions joint_update_node_safety Member) as [count [tail [Position [Safe Nonreg]]]].
 eapply formal_combinational_known_node; [exact Position|exact Safe|exact Nonreg| |reflexivity|exact Step].
 cbn [rfa_node_1109_expr eval_hfexpr_validif_policy eval_href_validif_policy]. exact Source.
Qed.
Theorem rfa_reset_history_1109 inputs path history limit :
 (forall t, (t < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history t) false (history t) flat_statements = Some (history (S t))) ->
 forall t, (4 <= t)%coq_nat -> (t <= limit)%coq_nat ->
 VM.find 1109 (history t) = Some (Gval (Fuint 32) (rfa_reset_word_24 inputs path)).
Proof.
 intros Steps t Lower Upper. destruct t as [|t]; [lia|].
 apply (rfa_reset_step_1109 inputs path (history t) (history t) (history (S t))).
 - apply (rfa_reset_history_811 inputs path history limit Steps t);lia.
 - apply Steps;lia.
Qed.
Definition rfa_wire_1506_decl := match straight_drop 1586 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition rfa_wire_1506_tail := match straight_drop 8995 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition rfa_wire_1506_mid := take_statements 7408 rfa_wire_1506_decl.
Lemma rfa_wire_1506_position : straight_drop 1585 flat_statements = Some (@Qcons VarOrder.T (@Swire VarOrder.T 1506 (Gtyp (Fuint 32))) rfa_wire_1506_decl).
Proof. vm_compute. reflexivity. Qed.
Lemma rfa_wire_1506_split : rfa_wire_1506_decl = statement_append rfa_wire_1506_mid (@Qcons VarOrder.T (@Sfcnct VarOrder.T (@Eid VarOrder.T 1506) (@Eref VarOrder.T (@Eid VarOrder.T 8138))) rfa_wire_1506_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma rfa_wire_1506_straight : straight_statements rfa_wire_1506_mid.
Proof. vm_compute. exact I. Qed.
Lemma rfa_wire_1506_mid_safe : formal_typed_suffix_safe flat_memories 1506 rfa_wire_1506_mid.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma rfa_wire_1506_tail_safe : formal_typed_suffix_safe flat_memories 1506 rfa_wire_1506_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma rfa_wire_1506_nonreg : has_register 1506 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem rfa_reset_step_1506 inputs path old current result :
 VM.find 8138 old = Some (Gval (Fuint 32) (rfa_reset_word_24 inputs path)) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 VM.find 1506 result = Some (Gval (Fuint 32) (rfa_reset_word_24 inputs path)).
Proof.
 intros Source Step.
 apply (declared_connection_value 1585 flat_statements rfa_wire_1506_decl rfa_wire_1506_mid rfa_wire_1506_tail 1506 8138 32
 (Gval (Fuint 32) (rfa_reset_word_24 inputs path)) (Gval (Fuint 32) (rfa_reset_word_24 inputs path))
 (formal_invalid_policy inputs path) flat_memories old current result rfa_wire_1506_position rfa_wire_1506_split rfa_wire_1506_straight rfa_wire_1506_mid_safe rfa_wire_1506_tail_safe rfa_wire_1506_nonreg (Logic.eq_refl _) Source).
 - assert (Take : take 32 (rfa_reset_word_24 inputs path) = rfa_reset_word_24 inputs path).
   { apply take_oversize. rewrite rfa_reset_word_24_size. reflexivity. }
   cbn [adapt_hvalue_as_type]. rewrite Take. unfold zext_to,zext. rewrite rfa_reset_word_24_size subnn cats0. reflexivity.
 - exact Step.
Qed.
Theorem rfa_reset_history_1506 inputs path history limit :
 (forall t, (t < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history t) false (history t) flat_statements = Some (history (S t))) ->
 forall t, (3 <= t)%coq_nat -> (t <= limit)%coq_nat ->
 VM.find 1506 (history t) = Some (Gval (Fuint 32) (rfa_reset_word_24 inputs path)).
Proof.
 intros Steps t Lower Upper. destruct t as [|t]; [lia|].
 apply (rfa_reset_step_1506 inputs path (history t) (history t) (history (S t))).
 - apply (rfa_reset_history_8138 inputs path history limit Steps t);lia.
 - apply Steps;lia.
Qed.
Definition rfa_wire_1696_decl := match straight_drop 1776 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition rfa_wire_1696_tail := match straight_drop 8247 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition rfa_wire_1696_mid := take_statements 6470 rfa_wire_1696_decl.
Lemma rfa_wire_1696_position : straight_drop 1775 flat_statements = Some (@Qcons VarOrder.T (@Swire VarOrder.T 1696 (Gtyp (Fuint 32))) rfa_wire_1696_decl).
Proof. vm_compute. reflexivity. Qed.
Lemma rfa_wire_1696_split : rfa_wire_1696_decl = statement_append rfa_wire_1696_mid (@Qcons VarOrder.T (@Sfcnct VarOrder.T (@Eid VarOrder.T 1696) (@Eref VarOrder.T (@Eid VarOrder.T 1506))) rfa_wire_1696_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma rfa_wire_1696_straight : straight_statements rfa_wire_1696_mid.
Proof. vm_compute. exact I. Qed.
Lemma rfa_wire_1696_mid_safe : formal_typed_suffix_safe flat_memories 1696 rfa_wire_1696_mid.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma rfa_wire_1696_tail_safe : formal_typed_suffix_safe flat_memories 1696 rfa_wire_1696_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma rfa_wire_1696_nonreg : has_register 1696 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem rfa_reset_step_1696 inputs path old current result :
 VM.find 1506 old = Some (Gval (Fuint 32) (rfa_reset_word_24 inputs path)) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 VM.find 1696 result = Some (Gval (Fuint 32) (rfa_reset_word_24 inputs path)).
Proof.
 intros Source Step.
 apply (declared_connection_value 1775 flat_statements rfa_wire_1696_decl rfa_wire_1696_mid rfa_wire_1696_tail 1696 1506 32
 (Gval (Fuint 32) (rfa_reset_word_24 inputs path)) (Gval (Fuint 32) (rfa_reset_word_24 inputs path))
 (formal_invalid_policy inputs path) flat_memories old current result rfa_wire_1696_position rfa_wire_1696_split rfa_wire_1696_straight rfa_wire_1696_mid_safe rfa_wire_1696_tail_safe rfa_wire_1696_nonreg (Logic.eq_refl _) Source).
 - assert (Take : take 32 (rfa_reset_word_24 inputs path) = rfa_reset_word_24 inputs path).
   { apply take_oversize. rewrite rfa_reset_word_24_size. reflexivity. }
   cbn [adapt_hvalue_as_type]. rewrite Take. unfold zext_to,zext. rewrite rfa_reset_word_24_size subnn cats0. reflexivity.
 - exact Step.
Qed.
Theorem rfa_reset_history_1696 inputs path history limit :
 (forall t, (t < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history t) false (history t) flat_statements = Some (history (S t))) ->
 forall t, (4 <= t)%coq_nat -> (t <= limit)%coq_nat ->
 VM.find 1696 (history t) = Some (Gval (Fuint 32) (rfa_reset_word_24 inputs path)).
Proof.
 intros Steps t Lower Upper. destruct t as [|t]; [lia|].
 apply (rfa_reset_step_1696 inputs path (history t) (history t) (history (S t))).
 - apply (rfa_reset_history_1506 inputs path history limit Steps t);lia.
 - apply Steps;lia.
Qed.
Definition rfa_node_7417_expr := (@Eref VarOrder.T (@Eid VarOrder.T 1696)).
Definition rfa_node_7417_tail := match straight_drop 7589 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma rfa_node_7417_position : straight_drop 7588 flat_statements = Some (@Qcons VarOrder.T (@Snode VarOrder.T 7417 rfa_node_7417_expr) rfa_node_7417_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma rfa_node_7417_safe : formal_typed_suffix_safe flat_memories 7417 rfa_node_7417_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma rfa_node_7417_nonreg : has_register 7417 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem rfa_reset_step_7417 inputs path old current result :
 VM.find 1696 old = Some (Gval (Fuint 32) (rfa_reset_word_24 inputs path)) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 VM.find 7417 result = Some (Gval (Fuint 32) (rfa_reset_word_24 inputs path)).
Proof.
 intros Source Step.
 eapply formal_combinational_known_node;
 [exact rfa_node_7417_position|exact rfa_node_7417_safe|exact rfa_node_7417_nonreg| |reflexivity|exact Step].
 cbn [rfa_node_7417_expr eval_hfexpr_validif_policy eval_href_validif_policy]. exact Source.
Qed.
Theorem rfa_reset_history_7417 inputs path history limit :
 (forall t, (t < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history t) false (history t) flat_statements = Some (history (S t))) ->
 forall t, (5 <= t)%coq_nat -> (t <= limit)%coq_nat ->
 VM.find 7417 (history t) = Some (Gval (Fuint 32) (rfa_reset_word_24 inputs path)).
Proof.
 intros Steps t Lower Upper. destruct t as [|t]; [lia|].
 apply (rfa_reset_step_7417 inputs path (history t) (history t) (history (S t))).
 - apply (rfa_reset_history_1696 inputs path history limit Steps t);lia.
 - apply Steps;lia.
Qed.
Definition rfa_node_7418_expr := (@Eref VarOrder.T (@Eid VarOrder.T 7417)).
Definition rfa_node_7418_tail := match straight_drop 7590 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma rfa_node_7418_position : straight_drop 7589 flat_statements = Some (@Qcons VarOrder.T (@Snode VarOrder.T 7418 rfa_node_7418_expr) rfa_node_7418_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma rfa_node_7418_safe : formal_typed_suffix_safe flat_memories 7418 rfa_node_7418_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma rfa_node_7418_nonreg : has_register 7418 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem rfa_reset_step_7418 inputs path old current result :
 VM.find 7417 old = Some (Gval (Fuint 32) (rfa_reset_word_24 inputs path)) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 VM.find 7418 result = Some (Gval (Fuint 32) (rfa_reset_word_24 inputs path)).
Proof.
 intros Source Step.
 eapply formal_combinational_known_node;
 [exact rfa_node_7418_position|exact rfa_node_7418_safe|exact rfa_node_7418_nonreg| |reflexivity|exact Step].
 cbn [rfa_node_7418_expr eval_hfexpr_validif_policy eval_href_validif_policy]. exact Source.
Qed.
Theorem rfa_reset_history_7418 inputs path history limit :
 (forall t, (t < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history t) false (history t) flat_statements = Some (history (S t))) ->
 forall t, (6 <= t)%coq_nat -> (t <= limit)%coq_nat ->
 VM.find 7418 (history t) = Some (Gval (Fuint 32) (rfa_reset_word_24 inputs path)).
Proof.
 intros Steps t Lower Upper. destruct t as [|t]; [lia|].
 apply (rfa_reset_step_7418 inputs path (history t) (history t) (history (S t))).
 - apply (rfa_reset_history_7417 inputs path history limit Steps t);lia.
 - apply Steps;lia.
Qed.
Definition rfa_reset_word_25 inputs path := proj1_sig (formal_symbolic_inputs inputs path (validif_source_address (validif_raw_address nil 8645 0 nil)) nil 32).
Lemma rfa_reset_word_25_size inputs path : size (rfa_reset_word_25 inputs path) = 32%nat.
Proof. exact (proj2_sig (formal_symbolic_inputs inputs path (validif_source_address (validif_raw_address nil 8645 0 nil)) nil 32)). Qed.
Definition rfa_node_8139_expr := (@Evalidif VarOrder.T (@Econst VarOrder.T (Fuint 1) [::false]) (@Econst VarOrder.T (Fuint 32) [::false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false])).
Definition rfa_node_8139_tail := match straight_drop 8646 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma rfa_node_8139_position : straight_drop 8645 flat_statements = Some (@Qcons VarOrder.T (@Snode VarOrder.T 8139 rfa_node_8139_expr) rfa_node_8139_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma rfa_node_8139_safe : formal_typed_suffix_safe flat_memories 8139 rfa_node_8139_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma rfa_node_8139_nonreg : has_register 8139 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem rfa_reset_step_8139 inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 VM.find 8139 result = Some (Gval (Fuint 32) (rfa_reset_word_25 inputs path)).
Proof.
 intros Step.
 eapply formal_combinational_known_node;
 [exact rfa_node_8139_position|exact rfa_node_8139_safe|exact rfa_node_8139_nonreg| |reflexivity|exact Step].
 reflexivity.
Qed.
Theorem rfa_reset_history_8139 inputs path history limit :
 (forall t, (t < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history t) false (history t) flat_statements = Some (history (S t))) ->
 forall t, (1 <= t)%coq_nat -> (t <= limit)%coq_nat ->
 VM.find 8139 (history t) = Some (Gval (Fuint 32) (rfa_reset_word_25 inputs path)).
Proof.
 intros Steps t Lower Upper. destruct t as [|t]; [lia|].
 apply (rfa_reset_step_8139 inputs path (history t) (history t) (history (S t))).
 apply Steps;lia.
Qed.
Definition rfa_node_8140_expr := joint_update_expr_8140.
Theorem rfa_reset_step_8140 inputs path old current result :
 VM.find 8139 old = Some (Gval (Fuint 32) (rfa_reset_word_25 inputs path)) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 VM.find 8140 result = Some (Gval (Fuint 32) (rfa_reset_word_25 inputs path)).
Proof.
 intros Source Step.
 assert (Member : List.In (8140,joint_update_expr_8140) joint_update_expected_nodes).
 { apply (List.nth_error_In joint_update_expected_nodes 1027%nat). vm_compute. reflexivity. }
 destruct (selected_node_safe_position flat_memories flat_statements joint_update_node_offsets flat_statements joint_update_expected_nodes 8140 joint_update_expr_8140 joint_update_node_positions joint_update_node_safety Member) as [count [tail [Position [Safe Nonreg]]]].
 eapply formal_combinational_known_node; [exact Position|exact Safe|exact Nonreg| |reflexivity|exact Step].
 cbn [rfa_node_8140_expr eval_hfexpr_validif_policy eval_href_validif_policy]. exact Source.
Qed.
Theorem rfa_reset_history_8140 inputs path history limit :
 (forall t, (t < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history t) false (history t) flat_statements = Some (history (S t))) ->
 forall t, (2 <= t)%coq_nat -> (t <= limit)%coq_nat ->
 VM.find 8140 (history t) = Some (Gval (Fuint 32) (rfa_reset_word_25 inputs path)).
Proof.
 intros Steps t Lower Upper. destruct t as [|t]; [lia|].
 apply (rfa_reset_step_8140 inputs path (history t) (history t) (history (S t))).
 - apply (rfa_reset_history_8139 inputs path history limit Steps t);lia.
 - apply Steps;lia.
Qed.
Lemma joint_update_connection_812_nonreg : has_register 812 flat_statements = false.
Proof. exact joint_update_connection_812_nonregister. Qed.
Theorem rfa_reset_step_812 inputs path old current result :
 VM.find 8140 old = Some (Gval (Fuint 32) (rfa_reset_word_25 inputs path)) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 VM.find 812 result = Some (Gval (Fuint 32) (rfa_reset_word_25 inputs path)).
Proof.
 intros Source Step.
 apply (declared_connection_value 821 flat_statements joint_update_connection_812_decl joint_update_connection_812_mid joint_update_connection_812_tail 812 8140 32
 (Gval (Fuint 32) (rfa_reset_word_25 inputs path)) (Gval (Fuint 32) (rfa_reset_word_25 inputs path))
 (formal_invalid_policy inputs path) flat_memories old current result joint_update_connection_812_position joint_update_connection_812_split joint_update_connection_812_straight joint_update_connection_812_mid_safe joint_update_connection_812_tail_safe joint_update_connection_812_nonreg (Logic.eq_refl _) Source).
 - assert (Take : take 32 (rfa_reset_word_25 inputs path) = rfa_reset_word_25 inputs path).
   { apply take_oversize. rewrite rfa_reset_word_25_size. reflexivity. }
   cbn [adapt_hvalue_as_type]. rewrite Take. unfold zext_to,zext. rewrite rfa_reset_word_25_size subnn cats0. reflexivity.
 - exact Step.
Qed.
Theorem rfa_reset_history_812 inputs path history limit :
 (forall t, (t < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history t) false (history t) flat_statements = Some (history (S t))) ->
 forall t, (3 <= t)%coq_nat -> (t <= limit)%coq_nat ->
 VM.find 812 (history t) = Some (Gval (Fuint 32) (rfa_reset_word_25 inputs path)).
Proof.
 intros Steps t Lower Upper. destruct t as [|t]; [lia|].
 apply (rfa_reset_step_812 inputs path (history t) (history t) (history (S t))).
 - apply (rfa_reset_history_8140 inputs path history limit Steps t);lia.
 - apply Steps;lia.
Qed.
Definition rfa_node_1110_expr := joint_update_expr_1110.
Theorem rfa_reset_step_1110 inputs path old current result :
 VM.find 812 old = Some (Gval (Fuint 32) (rfa_reset_word_25 inputs path)) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 VM.find 1110 result = Some (Gval (Fuint 32) (rfa_reset_word_25 inputs path)).
Proof.
 intros Source Step.
 assert (Member : List.In (1110,joint_update_expr_1110) joint_update_expected_nodes).
 { apply (List.nth_error_In joint_update_expected_nodes 700%nat). vm_compute. reflexivity. }
 destruct (selected_node_safe_position flat_memories flat_statements joint_update_node_offsets flat_statements joint_update_expected_nodes 1110 joint_update_expr_1110 joint_update_node_positions joint_update_node_safety Member) as [count [tail [Position [Safe Nonreg]]]].
 eapply formal_combinational_known_node; [exact Position|exact Safe|exact Nonreg| |reflexivity|exact Step].
 cbn [rfa_node_1110_expr eval_hfexpr_validif_policy eval_href_validif_policy]. exact Source.
Qed.
Theorem rfa_reset_history_1110 inputs path history limit :
 (forall t, (t < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history t) false (history t) flat_statements = Some (history (S t))) ->
 forall t, (4 <= t)%coq_nat -> (t <= limit)%coq_nat ->
 VM.find 1110 (history t) = Some (Gval (Fuint 32) (rfa_reset_word_25 inputs path)).
Proof.
 intros Steps t Lower Upper. destruct t as [|t]; [lia|].
 apply (rfa_reset_step_1110 inputs path (history t) (history t) (history (S t))).
 - apply (rfa_reset_history_812 inputs path history limit Steps t);lia.
 - apply Steps;lia.
Qed.
Definition rfa_wire_1507_decl := match straight_drop 1587 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition rfa_wire_1507_tail := match straight_drop 8996 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition rfa_wire_1507_mid := take_statements 7408 rfa_wire_1507_decl.
Lemma rfa_wire_1507_position : straight_drop 1586 flat_statements = Some (@Qcons VarOrder.T (@Swire VarOrder.T 1507 (Gtyp (Fuint 32))) rfa_wire_1507_decl).
Proof. vm_compute. reflexivity. Qed.
Lemma rfa_wire_1507_split : rfa_wire_1507_decl = statement_append rfa_wire_1507_mid (@Qcons VarOrder.T (@Sfcnct VarOrder.T (@Eid VarOrder.T 1507) (@Eref VarOrder.T (@Eid VarOrder.T 8140))) rfa_wire_1507_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma rfa_wire_1507_straight : straight_statements rfa_wire_1507_mid.
Proof. vm_compute. exact I. Qed.
Lemma rfa_wire_1507_mid_safe : formal_typed_suffix_safe flat_memories 1507 rfa_wire_1507_mid.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma rfa_wire_1507_tail_safe : formal_typed_suffix_safe flat_memories 1507 rfa_wire_1507_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma rfa_wire_1507_nonreg : has_register 1507 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem rfa_reset_step_1507 inputs path old current result :
 VM.find 8140 old = Some (Gval (Fuint 32) (rfa_reset_word_25 inputs path)) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 VM.find 1507 result = Some (Gval (Fuint 32) (rfa_reset_word_25 inputs path)).
Proof.
 intros Source Step.
 apply (declared_connection_value 1586 flat_statements rfa_wire_1507_decl rfa_wire_1507_mid rfa_wire_1507_tail 1507 8140 32
 (Gval (Fuint 32) (rfa_reset_word_25 inputs path)) (Gval (Fuint 32) (rfa_reset_word_25 inputs path))
 (formal_invalid_policy inputs path) flat_memories old current result rfa_wire_1507_position rfa_wire_1507_split rfa_wire_1507_straight rfa_wire_1507_mid_safe rfa_wire_1507_tail_safe rfa_wire_1507_nonreg (Logic.eq_refl _) Source).
 - assert (Take : take 32 (rfa_reset_word_25 inputs path) = rfa_reset_word_25 inputs path).
   { apply take_oversize. rewrite rfa_reset_word_25_size. reflexivity. }
   cbn [adapt_hvalue_as_type]. rewrite Take. unfold zext_to,zext. rewrite rfa_reset_word_25_size subnn cats0. reflexivity.
 - exact Step.
Qed.
Theorem rfa_reset_history_1507 inputs path history limit :
 (forall t, (t < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history t) false (history t) flat_statements = Some (history (S t))) ->
 forall t, (3 <= t)%coq_nat -> (t <= limit)%coq_nat ->
 VM.find 1507 (history t) = Some (Gval (Fuint 32) (rfa_reset_word_25 inputs path)).
Proof.
 intros Steps t Lower Upper. destruct t as [|t]; [lia|].
 apply (rfa_reset_step_1507 inputs path (history t) (history t) (history (S t))).
 - apply (rfa_reset_history_8140 inputs path history limit Steps t);lia.
 - apply Steps;lia.
Qed.
Definition rfa_wire_1697_decl := match straight_drop 1777 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition rfa_wire_1697_tail := match straight_drop 8248 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition rfa_wire_1697_mid := take_statements 6470 rfa_wire_1697_decl.
Lemma rfa_wire_1697_position : straight_drop 1776 flat_statements = Some (@Qcons VarOrder.T (@Swire VarOrder.T 1697 (Gtyp (Fuint 32))) rfa_wire_1697_decl).
Proof. vm_compute. reflexivity. Qed.
Lemma rfa_wire_1697_split : rfa_wire_1697_decl = statement_append rfa_wire_1697_mid (@Qcons VarOrder.T (@Sfcnct VarOrder.T (@Eid VarOrder.T 1697) (@Eref VarOrder.T (@Eid VarOrder.T 1507))) rfa_wire_1697_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma rfa_wire_1697_straight : straight_statements rfa_wire_1697_mid.
Proof. vm_compute. exact I. Qed.
Lemma rfa_wire_1697_mid_safe : formal_typed_suffix_safe flat_memories 1697 rfa_wire_1697_mid.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma rfa_wire_1697_tail_safe : formal_typed_suffix_safe flat_memories 1697 rfa_wire_1697_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma rfa_wire_1697_nonreg : has_register 1697 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem rfa_reset_step_1697 inputs path old current result :
 VM.find 1507 old = Some (Gval (Fuint 32) (rfa_reset_word_25 inputs path)) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 VM.find 1697 result = Some (Gval (Fuint 32) (rfa_reset_word_25 inputs path)).
Proof.
 intros Source Step.
 apply (declared_connection_value 1776 flat_statements rfa_wire_1697_decl rfa_wire_1697_mid rfa_wire_1697_tail 1697 1507 32
 (Gval (Fuint 32) (rfa_reset_word_25 inputs path)) (Gval (Fuint 32) (rfa_reset_word_25 inputs path))
 (formal_invalid_policy inputs path) flat_memories old current result rfa_wire_1697_position rfa_wire_1697_split rfa_wire_1697_straight rfa_wire_1697_mid_safe rfa_wire_1697_tail_safe rfa_wire_1697_nonreg (Logic.eq_refl _) Source).
 - assert (Take : take 32 (rfa_reset_word_25 inputs path) = rfa_reset_word_25 inputs path).
   { apply take_oversize. rewrite rfa_reset_word_25_size. reflexivity. }
   cbn [adapt_hvalue_as_type]. rewrite Take. unfold zext_to,zext. rewrite rfa_reset_word_25_size subnn cats0. reflexivity.
 - exact Step.
Qed.
Theorem rfa_reset_history_1697 inputs path history limit :
 (forall t, (t < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history t) false (history t) flat_statements = Some (history (S t))) ->
 forall t, (4 <= t)%coq_nat -> (t <= limit)%coq_nat ->
 VM.find 1697 (history t) = Some (Gval (Fuint 32) (rfa_reset_word_25 inputs path)).
Proof.
 intros Steps t Lower Upper. destruct t as [|t]; [lia|].
 apply (rfa_reset_step_1697 inputs path (history t) (history t) (history (S t))).
 - apply (rfa_reset_history_1507 inputs path history limit Steps t);lia.
 - apply Steps;lia.
Qed.
Definition rfa_node_7419_expr := (@Eref VarOrder.T (@Eid VarOrder.T 1697)).
Definition rfa_node_7419_tail := match straight_drop 7591 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma rfa_node_7419_position : straight_drop 7590 flat_statements = Some (@Qcons VarOrder.T (@Snode VarOrder.T 7419 rfa_node_7419_expr) rfa_node_7419_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma rfa_node_7419_safe : formal_typed_suffix_safe flat_memories 7419 rfa_node_7419_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma rfa_node_7419_nonreg : has_register 7419 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem rfa_reset_step_7419 inputs path old current result :
 VM.find 1697 old = Some (Gval (Fuint 32) (rfa_reset_word_25 inputs path)) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 VM.find 7419 result = Some (Gval (Fuint 32) (rfa_reset_word_25 inputs path)).
Proof.
 intros Source Step.
 eapply formal_combinational_known_node;
 [exact rfa_node_7419_position|exact rfa_node_7419_safe|exact rfa_node_7419_nonreg| |reflexivity|exact Step].
 cbn [rfa_node_7419_expr eval_hfexpr_validif_policy eval_href_validif_policy]. exact Source.
Qed.
Theorem rfa_reset_history_7419 inputs path history limit :
 (forall t, (t < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history t) false (history t) flat_statements = Some (history (S t))) ->
 forall t, (5 <= t)%coq_nat -> (t <= limit)%coq_nat ->
 VM.find 7419 (history t) = Some (Gval (Fuint 32) (rfa_reset_word_25 inputs path)).
Proof.
 intros Steps t Lower Upper. destruct t as [|t]; [lia|].
 apply (rfa_reset_step_7419 inputs path (history t) (history t) (history (S t))).
 - apply (rfa_reset_history_1697 inputs path history limit Steps t);lia.
 - apply Steps;lia.
Qed.
Definition rfa_node_7420_expr := (@Eref VarOrder.T (@Eid VarOrder.T 7419)).
Definition rfa_node_7420_tail := match straight_drop 7592 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma rfa_node_7420_position : straight_drop 7591 flat_statements = Some (@Qcons VarOrder.T (@Snode VarOrder.T 7420 rfa_node_7420_expr) rfa_node_7420_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma rfa_node_7420_safe : formal_typed_suffix_safe flat_memories 7420 rfa_node_7420_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma rfa_node_7420_nonreg : has_register 7420 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem rfa_reset_step_7420 inputs path old current result :
 VM.find 7419 old = Some (Gval (Fuint 32) (rfa_reset_word_25 inputs path)) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 VM.find 7420 result = Some (Gval (Fuint 32) (rfa_reset_word_25 inputs path)).
Proof.
 intros Source Step.
 eapply formal_combinational_known_node;
 [exact rfa_node_7420_position|exact rfa_node_7420_safe|exact rfa_node_7420_nonreg| |reflexivity|exact Step].
 cbn [rfa_node_7420_expr eval_hfexpr_validif_policy eval_href_validif_policy]. exact Source.
Qed.
Theorem rfa_reset_history_7420 inputs path history limit :
 (forall t, (t < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history t) false (history t) flat_statements = Some (history (S t))) ->
 forall t, (6 <= t)%coq_nat -> (t <= limit)%coq_nat ->
 VM.find 7420 (history t) = Some (Gval (Fuint 32) (rfa_reset_word_25 inputs path)).
Proof.
 intros Steps t Lower Upper. destruct t as [|t]; [lia|].
 apply (rfa_reset_step_7420 inputs path (history t) (history t) (history (S t))).
 - apply (rfa_reset_history_7419 inputs path history limit Steps t);lia.
 - apply Steps;lia.
Qed.
Definition rfa_reset_word_26 inputs path := proj1_sig (formal_symbolic_inputs inputs path (validif_source_address (validif_raw_address nil 8647 0 nil)) nil 32).
Lemma rfa_reset_word_26_size inputs path : size (rfa_reset_word_26 inputs path) = 32%nat.
Proof. exact (proj2_sig (formal_symbolic_inputs inputs path (validif_source_address (validif_raw_address nil 8647 0 nil)) nil 32)). Qed.
Definition rfa_node_8141_expr := (@Evalidif VarOrder.T (@Econst VarOrder.T (Fuint 1) [::false]) (@Econst VarOrder.T (Fuint 32) [::false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false])).
Definition rfa_node_8141_tail := match straight_drop 8648 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma rfa_node_8141_position : straight_drop 8647 flat_statements = Some (@Qcons VarOrder.T (@Snode VarOrder.T 8141 rfa_node_8141_expr) rfa_node_8141_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma rfa_node_8141_safe : formal_typed_suffix_safe flat_memories 8141 rfa_node_8141_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma rfa_node_8141_nonreg : has_register 8141 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem rfa_reset_step_8141 inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 VM.find 8141 result = Some (Gval (Fuint 32) (rfa_reset_word_26 inputs path)).
Proof.
 intros Step.
 eapply formal_combinational_known_node;
 [exact rfa_node_8141_position|exact rfa_node_8141_safe|exact rfa_node_8141_nonreg| |reflexivity|exact Step].
 reflexivity.
Qed.
Theorem rfa_reset_history_8141 inputs path history limit :
 (forall t, (t < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history t) false (history t) flat_statements = Some (history (S t))) ->
 forall t, (1 <= t)%coq_nat -> (t <= limit)%coq_nat ->
 VM.find 8141 (history t) = Some (Gval (Fuint 32) (rfa_reset_word_26 inputs path)).
Proof.
 intros Steps t Lower Upper. destruct t as [|t]; [lia|].
 apply (rfa_reset_step_8141 inputs path (history t) (history t) (history (S t))).
 apply Steps;lia.
Qed.
Definition rfa_node_8142_expr := joint_update_expr_8142.
Theorem rfa_reset_step_8142 inputs path old current result :
 VM.find 8141 old = Some (Gval (Fuint 32) (rfa_reset_word_26 inputs path)) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 VM.find 8142 result = Some (Gval (Fuint 32) (rfa_reset_word_26 inputs path)).
Proof.
 intros Source Step.
 assert (Member : List.In (8142,joint_update_expr_8142) joint_update_expected_nodes).
 { apply (List.nth_error_In joint_update_expected_nodes 1029%nat). vm_compute. reflexivity. }
 destruct (selected_node_safe_position flat_memories flat_statements joint_update_node_offsets flat_statements joint_update_expected_nodes 8142 joint_update_expr_8142 joint_update_node_positions joint_update_node_safety Member) as [count [tail [Position [Safe Nonreg]]]].
 eapply formal_combinational_known_node; [exact Position|exact Safe|exact Nonreg| |reflexivity|exact Step].
 cbn [rfa_node_8142_expr eval_hfexpr_validif_policy eval_href_validif_policy]. exact Source.
Qed.
Theorem rfa_reset_history_8142 inputs path history limit :
 (forall t, (t < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history t) false (history t) flat_statements = Some (history (S t))) ->
 forall t, (2 <= t)%coq_nat -> (t <= limit)%coq_nat ->
 VM.find 8142 (history t) = Some (Gval (Fuint 32) (rfa_reset_word_26 inputs path)).
Proof.
 intros Steps t Lower Upper. destruct t as [|t]; [lia|].
 apply (rfa_reset_step_8142 inputs path (history t) (history t) (history (S t))).
 - apply (rfa_reset_history_8141 inputs path history limit Steps t);lia.
 - apply Steps;lia.
Qed.
Lemma joint_update_connection_813_nonreg : has_register 813 flat_statements = false.
Proof. exact joint_update_connection_813_nonregister. Qed.
Theorem rfa_reset_step_813 inputs path old current result :
 VM.find 8142 old = Some (Gval (Fuint 32) (rfa_reset_word_26 inputs path)) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 VM.find 813 result = Some (Gval (Fuint 32) (rfa_reset_word_26 inputs path)).
Proof.
 intros Source Step.
 apply (declared_connection_value 822 flat_statements joint_update_connection_813_decl joint_update_connection_813_mid joint_update_connection_813_tail 813 8142 32
 (Gval (Fuint 32) (rfa_reset_word_26 inputs path)) (Gval (Fuint 32) (rfa_reset_word_26 inputs path))
 (formal_invalid_policy inputs path) flat_memories old current result joint_update_connection_813_position joint_update_connection_813_split joint_update_connection_813_straight joint_update_connection_813_mid_safe joint_update_connection_813_tail_safe joint_update_connection_813_nonreg (Logic.eq_refl _) Source).
 - assert (Take : take 32 (rfa_reset_word_26 inputs path) = rfa_reset_word_26 inputs path).
   { apply take_oversize. rewrite rfa_reset_word_26_size. reflexivity. }
   cbn [adapt_hvalue_as_type]. rewrite Take. unfold zext_to,zext. rewrite rfa_reset_word_26_size subnn cats0. reflexivity.
 - exact Step.
Qed.
Theorem rfa_reset_history_813 inputs path history limit :
 (forall t, (t < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history t) false (history t) flat_statements = Some (history (S t))) ->
 forall t, (3 <= t)%coq_nat -> (t <= limit)%coq_nat ->
 VM.find 813 (history t) = Some (Gval (Fuint 32) (rfa_reset_word_26 inputs path)).
Proof.
 intros Steps t Lower Upper. destruct t as [|t]; [lia|].
 apply (rfa_reset_step_813 inputs path (history t) (history t) (history (S t))).
 - apply (rfa_reset_history_8142 inputs path history limit Steps t);lia.
 - apply Steps;lia.
Qed.
Definition rfa_node_1111_expr := joint_update_expr_1111.
Theorem rfa_reset_step_1111 inputs path old current result :
 VM.find 813 old = Some (Gval (Fuint 32) (rfa_reset_word_26 inputs path)) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 VM.find 1111 result = Some (Gval (Fuint 32) (rfa_reset_word_26 inputs path)).
Proof.
 intros Source Step.
 assert (Member : List.In (1111,joint_update_expr_1111) joint_update_expected_nodes).
 { apply (List.nth_error_In joint_update_expected_nodes 701%nat). vm_compute. reflexivity. }
 destruct (selected_node_safe_position flat_memories flat_statements joint_update_node_offsets flat_statements joint_update_expected_nodes 1111 joint_update_expr_1111 joint_update_node_positions joint_update_node_safety Member) as [count [tail [Position [Safe Nonreg]]]].
 eapply formal_combinational_known_node; [exact Position|exact Safe|exact Nonreg| |reflexivity|exact Step].
 cbn [rfa_node_1111_expr eval_hfexpr_validif_policy eval_href_validif_policy]. exact Source.
Qed.
Theorem rfa_reset_history_1111 inputs path history limit :
 (forall t, (t < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history t) false (history t) flat_statements = Some (history (S t))) ->
 forall t, (4 <= t)%coq_nat -> (t <= limit)%coq_nat ->
 VM.find 1111 (history t) = Some (Gval (Fuint 32) (rfa_reset_word_26 inputs path)).
Proof.
 intros Steps t Lower Upper. destruct t as [|t]; [lia|].
 apply (rfa_reset_step_1111 inputs path (history t) (history t) (history (S t))).
 - apply (rfa_reset_history_813 inputs path history limit Steps t);lia.
 - apply Steps;lia.
Qed.
Definition rfa_wire_1508_decl := match straight_drop 1588 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition rfa_wire_1508_tail := match straight_drop 8997 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition rfa_wire_1508_mid := take_statements 7408 rfa_wire_1508_decl.
Lemma rfa_wire_1508_position : straight_drop 1587 flat_statements = Some (@Qcons VarOrder.T (@Swire VarOrder.T 1508 (Gtyp (Fuint 32))) rfa_wire_1508_decl).
Proof. vm_compute. reflexivity. Qed.
Lemma rfa_wire_1508_split : rfa_wire_1508_decl = statement_append rfa_wire_1508_mid (@Qcons VarOrder.T (@Sfcnct VarOrder.T (@Eid VarOrder.T 1508) (@Eref VarOrder.T (@Eid VarOrder.T 8142))) rfa_wire_1508_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma rfa_wire_1508_straight : straight_statements rfa_wire_1508_mid.
Proof. vm_compute. exact I. Qed.
Lemma rfa_wire_1508_mid_safe : formal_typed_suffix_safe flat_memories 1508 rfa_wire_1508_mid.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma rfa_wire_1508_tail_safe : formal_typed_suffix_safe flat_memories 1508 rfa_wire_1508_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma rfa_wire_1508_nonreg : has_register 1508 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem rfa_reset_step_1508 inputs path old current result :
 VM.find 8142 old = Some (Gval (Fuint 32) (rfa_reset_word_26 inputs path)) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 VM.find 1508 result = Some (Gval (Fuint 32) (rfa_reset_word_26 inputs path)).
Proof.
 intros Source Step.
 apply (declared_connection_value 1587 flat_statements rfa_wire_1508_decl rfa_wire_1508_mid rfa_wire_1508_tail 1508 8142 32
 (Gval (Fuint 32) (rfa_reset_word_26 inputs path)) (Gval (Fuint 32) (rfa_reset_word_26 inputs path))
 (formal_invalid_policy inputs path) flat_memories old current result rfa_wire_1508_position rfa_wire_1508_split rfa_wire_1508_straight rfa_wire_1508_mid_safe rfa_wire_1508_tail_safe rfa_wire_1508_nonreg (Logic.eq_refl _) Source).
 - assert (Take : take 32 (rfa_reset_word_26 inputs path) = rfa_reset_word_26 inputs path).
   { apply take_oversize. rewrite rfa_reset_word_26_size. reflexivity. }
   cbn [adapt_hvalue_as_type]. rewrite Take. unfold zext_to,zext. rewrite rfa_reset_word_26_size subnn cats0. reflexivity.
 - exact Step.
Qed.
Theorem rfa_reset_history_1508 inputs path history limit :
 (forall t, (t < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history t) false (history t) flat_statements = Some (history (S t))) ->
 forall t, (3 <= t)%coq_nat -> (t <= limit)%coq_nat ->
 VM.find 1508 (history t) = Some (Gval (Fuint 32) (rfa_reset_word_26 inputs path)).
Proof.
 intros Steps t Lower Upper. destruct t as [|t]; [lia|].
 apply (rfa_reset_step_1508 inputs path (history t) (history t) (history (S t))).
 - apply (rfa_reset_history_8142 inputs path history limit Steps t);lia.
 - apply Steps;lia.
Qed.
Definition rfa_wire_1698_decl := match straight_drop 1778 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition rfa_wire_1698_tail := match straight_drop 8249 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition rfa_wire_1698_mid := take_statements 6470 rfa_wire_1698_decl.
Lemma rfa_wire_1698_position : straight_drop 1777 flat_statements = Some (@Qcons VarOrder.T (@Swire VarOrder.T 1698 (Gtyp (Fuint 32))) rfa_wire_1698_decl).
Proof. vm_compute. reflexivity. Qed.
Lemma rfa_wire_1698_split : rfa_wire_1698_decl = statement_append rfa_wire_1698_mid (@Qcons VarOrder.T (@Sfcnct VarOrder.T (@Eid VarOrder.T 1698) (@Eref VarOrder.T (@Eid VarOrder.T 1508))) rfa_wire_1698_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma rfa_wire_1698_straight : straight_statements rfa_wire_1698_mid.
Proof. vm_compute. exact I. Qed.
Lemma rfa_wire_1698_mid_safe : formal_typed_suffix_safe flat_memories 1698 rfa_wire_1698_mid.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma rfa_wire_1698_tail_safe : formal_typed_suffix_safe flat_memories 1698 rfa_wire_1698_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma rfa_wire_1698_nonreg : has_register 1698 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem rfa_reset_step_1698 inputs path old current result :
 VM.find 1508 old = Some (Gval (Fuint 32) (rfa_reset_word_26 inputs path)) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 VM.find 1698 result = Some (Gval (Fuint 32) (rfa_reset_word_26 inputs path)).
Proof.
 intros Source Step.
 apply (declared_connection_value 1777 flat_statements rfa_wire_1698_decl rfa_wire_1698_mid rfa_wire_1698_tail 1698 1508 32
 (Gval (Fuint 32) (rfa_reset_word_26 inputs path)) (Gval (Fuint 32) (rfa_reset_word_26 inputs path))
 (formal_invalid_policy inputs path) flat_memories old current result rfa_wire_1698_position rfa_wire_1698_split rfa_wire_1698_straight rfa_wire_1698_mid_safe rfa_wire_1698_tail_safe rfa_wire_1698_nonreg (Logic.eq_refl _) Source).
 - assert (Take : take 32 (rfa_reset_word_26 inputs path) = rfa_reset_word_26 inputs path).
   { apply take_oversize. rewrite rfa_reset_word_26_size. reflexivity. }
   cbn [adapt_hvalue_as_type]. rewrite Take. unfold zext_to,zext. rewrite rfa_reset_word_26_size subnn cats0. reflexivity.
 - exact Step.
Qed.
Theorem rfa_reset_history_1698 inputs path history limit :
 (forall t, (t < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history t) false (history t) flat_statements = Some (history (S t))) ->
 forall t, (4 <= t)%coq_nat -> (t <= limit)%coq_nat ->
 VM.find 1698 (history t) = Some (Gval (Fuint 32) (rfa_reset_word_26 inputs path)).
Proof.
 intros Steps t Lower Upper. destruct t as [|t]; [lia|].
 apply (rfa_reset_step_1698 inputs path (history t) (history t) (history (S t))).
 - apply (rfa_reset_history_1508 inputs path history limit Steps t);lia.
 - apply Steps;lia.
Qed.
Definition rfa_node_7421_expr := (@Eref VarOrder.T (@Eid VarOrder.T 1698)).
Definition rfa_node_7421_tail := match straight_drop 7593 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma rfa_node_7421_position : straight_drop 7592 flat_statements = Some (@Qcons VarOrder.T (@Snode VarOrder.T 7421 rfa_node_7421_expr) rfa_node_7421_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma rfa_node_7421_safe : formal_typed_suffix_safe flat_memories 7421 rfa_node_7421_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma rfa_node_7421_nonreg : has_register 7421 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem rfa_reset_step_7421 inputs path old current result :
 VM.find 1698 old = Some (Gval (Fuint 32) (rfa_reset_word_26 inputs path)) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 VM.find 7421 result = Some (Gval (Fuint 32) (rfa_reset_word_26 inputs path)).
Proof.
 intros Source Step.
 eapply formal_combinational_known_node;
 [exact rfa_node_7421_position|exact rfa_node_7421_safe|exact rfa_node_7421_nonreg| |reflexivity|exact Step].
 cbn [rfa_node_7421_expr eval_hfexpr_validif_policy eval_href_validif_policy]. exact Source.
Qed.
Theorem rfa_reset_history_7421 inputs path history limit :
 (forall t, (t < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history t) false (history t) flat_statements = Some (history (S t))) ->
 forall t, (5 <= t)%coq_nat -> (t <= limit)%coq_nat ->
 VM.find 7421 (history t) = Some (Gval (Fuint 32) (rfa_reset_word_26 inputs path)).
Proof.
 intros Steps t Lower Upper. destruct t as [|t]; [lia|].
 apply (rfa_reset_step_7421 inputs path (history t) (history t) (history (S t))).
 - apply (rfa_reset_history_1698 inputs path history limit Steps t);lia.
 - apply Steps;lia.
Qed.
Definition rfa_node_7422_expr := (@Eref VarOrder.T (@Eid VarOrder.T 7421)).
Definition rfa_node_7422_tail := match straight_drop 7594 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma rfa_node_7422_position : straight_drop 7593 flat_statements = Some (@Qcons VarOrder.T (@Snode VarOrder.T 7422 rfa_node_7422_expr) rfa_node_7422_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma rfa_node_7422_safe : formal_typed_suffix_safe flat_memories 7422 rfa_node_7422_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma rfa_node_7422_nonreg : has_register 7422 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem rfa_reset_step_7422 inputs path old current result :
 VM.find 7421 old = Some (Gval (Fuint 32) (rfa_reset_word_26 inputs path)) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 VM.find 7422 result = Some (Gval (Fuint 32) (rfa_reset_word_26 inputs path)).
Proof.
 intros Source Step.
 eapply formal_combinational_known_node;
 [exact rfa_node_7422_position|exact rfa_node_7422_safe|exact rfa_node_7422_nonreg| |reflexivity|exact Step].
 cbn [rfa_node_7422_expr eval_hfexpr_validif_policy eval_href_validif_policy]. exact Source.
Qed.
Theorem rfa_reset_history_7422 inputs path history limit :
 (forall t, (t < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history t) false (history t) flat_statements = Some (history (S t))) ->
 forall t, (6 <= t)%coq_nat -> (t <= limit)%coq_nat ->
 VM.find 7422 (history t) = Some (Gval (Fuint 32) (rfa_reset_word_26 inputs path)).
Proof.
 intros Steps t Lower Upper. destruct t as [|t]; [lia|].
 apply (rfa_reset_step_7422 inputs path (history t) (history t) (history (S t))).
 - apply (rfa_reset_history_7421 inputs path history limit Steps t);lia.
 - apply Steps;lia.
Qed.
Definition rfa_reset_word_27 inputs path := proj1_sig (formal_symbolic_inputs inputs path (validif_source_address (validif_raw_address nil 8649 0 nil)) nil 32).
Lemma rfa_reset_word_27_size inputs path : size (rfa_reset_word_27 inputs path) = 32%nat.
Proof. exact (proj2_sig (formal_symbolic_inputs inputs path (validif_source_address (validif_raw_address nil 8649 0 nil)) nil 32)). Qed.
Definition rfa_node_8143_expr := (@Evalidif VarOrder.T (@Econst VarOrder.T (Fuint 1) [::false]) (@Econst VarOrder.T (Fuint 32) [::false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false])).
Definition rfa_node_8143_tail := match straight_drop 8650 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma rfa_node_8143_position : straight_drop 8649 flat_statements = Some (@Qcons VarOrder.T (@Snode VarOrder.T 8143 rfa_node_8143_expr) rfa_node_8143_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma rfa_node_8143_safe : formal_typed_suffix_safe flat_memories 8143 rfa_node_8143_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma rfa_node_8143_nonreg : has_register 8143 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem rfa_reset_step_8143 inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 VM.find 8143 result = Some (Gval (Fuint 32) (rfa_reset_word_27 inputs path)).
Proof.
 intros Step.
 eapply formal_combinational_known_node;
 [exact rfa_node_8143_position|exact rfa_node_8143_safe|exact rfa_node_8143_nonreg| |reflexivity|exact Step].
 reflexivity.
Qed.
Theorem rfa_reset_history_8143 inputs path history limit :
 (forall t, (t < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history t) false (history t) flat_statements = Some (history (S t))) ->
 forall t, (1 <= t)%coq_nat -> (t <= limit)%coq_nat ->
 VM.find 8143 (history t) = Some (Gval (Fuint 32) (rfa_reset_word_27 inputs path)).
Proof.
 intros Steps t Lower Upper. destruct t as [|t]; [lia|].
 apply (rfa_reset_step_8143 inputs path (history t) (history t) (history (S t))).
 apply Steps;lia.
Qed.
Definition rfa_node_8144_expr := joint_update_expr_8144.
Theorem rfa_reset_step_8144 inputs path old current result :
 VM.find 8143 old = Some (Gval (Fuint 32) (rfa_reset_word_27 inputs path)) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 VM.find 8144 result = Some (Gval (Fuint 32) (rfa_reset_word_27 inputs path)).
Proof.
 intros Source Step.
 assert (Member : List.In (8144,joint_update_expr_8144) joint_update_expected_nodes).
 { apply (List.nth_error_In joint_update_expected_nodes 1031%nat). vm_compute. reflexivity. }
 destruct (selected_node_safe_position flat_memories flat_statements joint_update_node_offsets flat_statements joint_update_expected_nodes 8144 joint_update_expr_8144 joint_update_node_positions joint_update_node_safety Member) as [count [tail [Position [Safe Nonreg]]]].
 eapply formal_combinational_known_node; [exact Position|exact Safe|exact Nonreg| |reflexivity|exact Step].
 cbn [rfa_node_8144_expr eval_hfexpr_validif_policy eval_href_validif_policy]. exact Source.
Qed.
Theorem rfa_reset_history_8144 inputs path history limit :
 (forall t, (t < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history t) false (history t) flat_statements = Some (history (S t))) ->
 forall t, (2 <= t)%coq_nat -> (t <= limit)%coq_nat ->
 VM.find 8144 (history t) = Some (Gval (Fuint 32) (rfa_reset_word_27 inputs path)).
Proof.
 intros Steps t Lower Upper. destruct t as [|t]; [lia|].
 apply (rfa_reset_step_8144 inputs path (history t) (history t) (history (S t))).
 - apply (rfa_reset_history_8143 inputs path history limit Steps t);lia.
 - apply Steps;lia.
Qed.
Lemma joint_update_connection_814_nonreg : has_register 814 flat_statements = false.
Proof. exact joint_update_connection_814_nonregister. Qed.
Theorem rfa_reset_step_814 inputs path old current result :
 VM.find 8144 old = Some (Gval (Fuint 32) (rfa_reset_word_27 inputs path)) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 VM.find 814 result = Some (Gval (Fuint 32) (rfa_reset_word_27 inputs path)).
Proof.
 intros Source Step.
 apply (declared_connection_value 823 flat_statements joint_update_connection_814_decl joint_update_connection_814_mid joint_update_connection_814_tail 814 8144 32
 (Gval (Fuint 32) (rfa_reset_word_27 inputs path)) (Gval (Fuint 32) (rfa_reset_word_27 inputs path))
 (formal_invalid_policy inputs path) flat_memories old current result joint_update_connection_814_position joint_update_connection_814_split joint_update_connection_814_straight joint_update_connection_814_mid_safe joint_update_connection_814_tail_safe joint_update_connection_814_nonreg (Logic.eq_refl _) Source).
 - assert (Take : take 32 (rfa_reset_word_27 inputs path) = rfa_reset_word_27 inputs path).
   { apply take_oversize. rewrite rfa_reset_word_27_size. reflexivity. }
   cbn [adapt_hvalue_as_type]. rewrite Take. unfold zext_to,zext. rewrite rfa_reset_word_27_size subnn cats0. reflexivity.
 - exact Step.
Qed.
Theorem rfa_reset_history_814 inputs path history limit :
 (forall t, (t < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history t) false (history t) flat_statements = Some (history (S t))) ->
 forall t, (3 <= t)%coq_nat -> (t <= limit)%coq_nat ->
 VM.find 814 (history t) = Some (Gval (Fuint 32) (rfa_reset_word_27 inputs path)).
Proof.
 intros Steps t Lower Upper. destruct t as [|t]; [lia|].
 apply (rfa_reset_step_814 inputs path (history t) (history t) (history (S t))).
 - apply (rfa_reset_history_8144 inputs path history limit Steps t);lia.
 - apply Steps;lia.
Qed.
Definition rfa_node_1112_expr := joint_update_expr_1112.
Theorem rfa_reset_step_1112 inputs path old current result :
 VM.find 814 old = Some (Gval (Fuint 32) (rfa_reset_word_27 inputs path)) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 VM.find 1112 result = Some (Gval (Fuint 32) (rfa_reset_word_27 inputs path)).
Proof.
 intros Source Step.
 assert (Member : List.In (1112,joint_update_expr_1112) joint_update_expected_nodes).
 { apply (List.nth_error_In joint_update_expected_nodes 702%nat). vm_compute. reflexivity. }
 destruct (selected_node_safe_position flat_memories flat_statements joint_update_node_offsets flat_statements joint_update_expected_nodes 1112 joint_update_expr_1112 joint_update_node_positions joint_update_node_safety Member) as [count [tail [Position [Safe Nonreg]]]].
 eapply formal_combinational_known_node; [exact Position|exact Safe|exact Nonreg| |reflexivity|exact Step].
 cbn [rfa_node_1112_expr eval_hfexpr_validif_policy eval_href_validif_policy]. exact Source.
Qed.
Theorem rfa_reset_history_1112 inputs path history limit :
 (forall t, (t < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history t) false (history t) flat_statements = Some (history (S t))) ->
 forall t, (4 <= t)%coq_nat -> (t <= limit)%coq_nat ->
 VM.find 1112 (history t) = Some (Gval (Fuint 32) (rfa_reset_word_27 inputs path)).
Proof.
 intros Steps t Lower Upper. destruct t as [|t]; [lia|].
 apply (rfa_reset_step_1112 inputs path (history t) (history t) (history (S t))).
 - apply (rfa_reset_history_814 inputs path history limit Steps t);lia.
 - apply Steps;lia.
Qed.
Definition rfa_wire_1509_decl := match straight_drop 1589 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition rfa_wire_1509_tail := match straight_drop 8998 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition rfa_wire_1509_mid := take_statements 7408 rfa_wire_1509_decl.
Lemma rfa_wire_1509_position : straight_drop 1588 flat_statements = Some (@Qcons VarOrder.T (@Swire VarOrder.T 1509 (Gtyp (Fuint 32))) rfa_wire_1509_decl).
Proof. vm_compute. reflexivity. Qed.
Lemma rfa_wire_1509_split : rfa_wire_1509_decl = statement_append rfa_wire_1509_mid (@Qcons VarOrder.T (@Sfcnct VarOrder.T (@Eid VarOrder.T 1509) (@Eref VarOrder.T (@Eid VarOrder.T 8144))) rfa_wire_1509_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma rfa_wire_1509_straight : straight_statements rfa_wire_1509_mid.
Proof. vm_compute. exact I. Qed.
Lemma rfa_wire_1509_mid_safe : formal_typed_suffix_safe flat_memories 1509 rfa_wire_1509_mid.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma rfa_wire_1509_tail_safe : formal_typed_suffix_safe flat_memories 1509 rfa_wire_1509_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma rfa_wire_1509_nonreg : has_register 1509 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem rfa_reset_step_1509 inputs path old current result :
 VM.find 8144 old = Some (Gval (Fuint 32) (rfa_reset_word_27 inputs path)) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 VM.find 1509 result = Some (Gval (Fuint 32) (rfa_reset_word_27 inputs path)).
Proof.
 intros Source Step.
 apply (declared_connection_value 1588 flat_statements rfa_wire_1509_decl rfa_wire_1509_mid rfa_wire_1509_tail 1509 8144 32
 (Gval (Fuint 32) (rfa_reset_word_27 inputs path)) (Gval (Fuint 32) (rfa_reset_word_27 inputs path))
 (formal_invalid_policy inputs path) flat_memories old current result rfa_wire_1509_position rfa_wire_1509_split rfa_wire_1509_straight rfa_wire_1509_mid_safe rfa_wire_1509_tail_safe rfa_wire_1509_nonreg (Logic.eq_refl _) Source).
 - assert (Take : take 32 (rfa_reset_word_27 inputs path) = rfa_reset_word_27 inputs path).
   { apply take_oversize. rewrite rfa_reset_word_27_size. reflexivity. }
   cbn [adapt_hvalue_as_type]. rewrite Take. unfold zext_to,zext. rewrite rfa_reset_word_27_size subnn cats0. reflexivity.
 - exact Step.
Qed.
Theorem rfa_reset_history_1509 inputs path history limit :
 (forall t, (t < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history t) false (history t) flat_statements = Some (history (S t))) ->
 forall t, (3 <= t)%coq_nat -> (t <= limit)%coq_nat ->
 VM.find 1509 (history t) = Some (Gval (Fuint 32) (rfa_reset_word_27 inputs path)).
Proof.
 intros Steps t Lower Upper. destruct t as [|t]; [lia|].
 apply (rfa_reset_step_1509 inputs path (history t) (history t) (history (S t))).
 - apply (rfa_reset_history_8144 inputs path history limit Steps t);lia.
 - apply Steps;lia.
Qed.
Definition rfa_wire_1699_decl := match straight_drop 1779 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition rfa_wire_1699_tail := match straight_drop 8250 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition rfa_wire_1699_mid := take_statements 6470 rfa_wire_1699_decl.
Lemma rfa_wire_1699_position : straight_drop 1778 flat_statements = Some (@Qcons VarOrder.T (@Swire VarOrder.T 1699 (Gtyp (Fuint 32))) rfa_wire_1699_decl).
Proof. vm_compute. reflexivity. Qed.
Lemma rfa_wire_1699_split : rfa_wire_1699_decl = statement_append rfa_wire_1699_mid (@Qcons VarOrder.T (@Sfcnct VarOrder.T (@Eid VarOrder.T 1699) (@Eref VarOrder.T (@Eid VarOrder.T 1509))) rfa_wire_1699_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma rfa_wire_1699_straight : straight_statements rfa_wire_1699_mid.
Proof. vm_compute. exact I. Qed.
Lemma rfa_wire_1699_mid_safe : formal_typed_suffix_safe flat_memories 1699 rfa_wire_1699_mid.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma rfa_wire_1699_tail_safe : formal_typed_suffix_safe flat_memories 1699 rfa_wire_1699_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma rfa_wire_1699_nonreg : has_register 1699 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem rfa_reset_step_1699 inputs path old current result :
 VM.find 1509 old = Some (Gval (Fuint 32) (rfa_reset_word_27 inputs path)) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 VM.find 1699 result = Some (Gval (Fuint 32) (rfa_reset_word_27 inputs path)).
Proof.
 intros Source Step.
 apply (declared_connection_value 1778 flat_statements rfa_wire_1699_decl rfa_wire_1699_mid rfa_wire_1699_tail 1699 1509 32
 (Gval (Fuint 32) (rfa_reset_word_27 inputs path)) (Gval (Fuint 32) (rfa_reset_word_27 inputs path))
 (formal_invalid_policy inputs path) flat_memories old current result rfa_wire_1699_position rfa_wire_1699_split rfa_wire_1699_straight rfa_wire_1699_mid_safe rfa_wire_1699_tail_safe rfa_wire_1699_nonreg (Logic.eq_refl _) Source).
 - assert (Take : take 32 (rfa_reset_word_27 inputs path) = rfa_reset_word_27 inputs path).
   { apply take_oversize. rewrite rfa_reset_word_27_size. reflexivity. }
   cbn [adapt_hvalue_as_type]. rewrite Take. unfold zext_to,zext. rewrite rfa_reset_word_27_size subnn cats0. reflexivity.
 - exact Step.
Qed.
Theorem rfa_reset_history_1699 inputs path history limit :
 (forall t, (t < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history t) false (history t) flat_statements = Some (history (S t))) ->
 forall t, (4 <= t)%coq_nat -> (t <= limit)%coq_nat ->
 VM.find 1699 (history t) = Some (Gval (Fuint 32) (rfa_reset_word_27 inputs path)).
Proof.
 intros Steps t Lower Upper. destruct t as [|t]; [lia|].
 apply (rfa_reset_step_1699 inputs path (history t) (history t) (history (S t))).
 - apply (rfa_reset_history_1509 inputs path history limit Steps t);lia.
 - apply Steps;lia.
Qed.
Definition rfa_node_7423_expr := (@Eref VarOrder.T (@Eid VarOrder.T 1699)).
Definition rfa_node_7423_tail := match straight_drop 7595 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma rfa_node_7423_position : straight_drop 7594 flat_statements = Some (@Qcons VarOrder.T (@Snode VarOrder.T 7423 rfa_node_7423_expr) rfa_node_7423_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma rfa_node_7423_safe : formal_typed_suffix_safe flat_memories 7423 rfa_node_7423_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma rfa_node_7423_nonreg : has_register 7423 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem rfa_reset_step_7423 inputs path old current result :
 VM.find 1699 old = Some (Gval (Fuint 32) (rfa_reset_word_27 inputs path)) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 VM.find 7423 result = Some (Gval (Fuint 32) (rfa_reset_word_27 inputs path)).
Proof.
 intros Source Step.
 eapply formal_combinational_known_node;
 [exact rfa_node_7423_position|exact rfa_node_7423_safe|exact rfa_node_7423_nonreg| |reflexivity|exact Step].
 cbn [rfa_node_7423_expr eval_hfexpr_validif_policy eval_href_validif_policy]. exact Source.
Qed.
Theorem rfa_reset_history_7423 inputs path history limit :
 (forall t, (t < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history t) false (history t) flat_statements = Some (history (S t))) ->
 forall t, (5 <= t)%coq_nat -> (t <= limit)%coq_nat ->
 VM.find 7423 (history t) = Some (Gval (Fuint 32) (rfa_reset_word_27 inputs path)).
Proof.
 intros Steps t Lower Upper. destruct t as [|t]; [lia|].
 apply (rfa_reset_step_7423 inputs path (history t) (history t) (history (S t))).
 - apply (rfa_reset_history_1699 inputs path history limit Steps t);lia.
 - apply Steps;lia.
Qed.
Definition rfa_node_7424_expr := (@Eref VarOrder.T (@Eid VarOrder.T 7423)).
Definition rfa_node_7424_tail := match straight_drop 7596 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma rfa_node_7424_position : straight_drop 7595 flat_statements = Some (@Qcons VarOrder.T (@Snode VarOrder.T 7424 rfa_node_7424_expr) rfa_node_7424_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma rfa_node_7424_safe : formal_typed_suffix_safe flat_memories 7424 rfa_node_7424_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma rfa_node_7424_nonreg : has_register 7424 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem rfa_reset_step_7424 inputs path old current result :
 VM.find 7423 old = Some (Gval (Fuint 32) (rfa_reset_word_27 inputs path)) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 VM.find 7424 result = Some (Gval (Fuint 32) (rfa_reset_word_27 inputs path)).
Proof.
 intros Source Step.
 eapply formal_combinational_known_node;
 [exact rfa_node_7424_position|exact rfa_node_7424_safe|exact rfa_node_7424_nonreg| |reflexivity|exact Step].
 cbn [rfa_node_7424_expr eval_hfexpr_validif_policy eval_href_validif_policy]. exact Source.
Qed.
Theorem rfa_reset_history_7424 inputs path history limit :
 (forall t, (t < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history t) false (history t) flat_statements = Some (history (S t))) ->
 forall t, (6 <= t)%coq_nat -> (t <= limit)%coq_nat ->
 VM.find 7424 (history t) = Some (Gval (Fuint 32) (rfa_reset_word_27 inputs path)).
Proof.
 intros Steps t Lower Upper. destruct t as [|t]; [lia|].
 apply (rfa_reset_step_7424 inputs path (history t) (history t) (history (S t))).
 - apply (rfa_reset_history_7423 inputs path history limit Steps t);lia.
 - apply Steps;lia.
Qed.
