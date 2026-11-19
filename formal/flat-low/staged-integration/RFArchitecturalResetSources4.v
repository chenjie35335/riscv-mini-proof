Require Import SelectedNodeSafety JointUpdateNodePositions JointUpdateExpressionCertificates JointUpdateConnectionCertificates CoreSocModel ComparisonNodes ScalarNodeFrames FormalTypedNodeFrames RegisterInvariants FormalTypedNodeEquation FormalDeclaredConnection FormalStatementSegments RegisterCommitCertificate FormalUIntRegisterCommitSource SelectedUIntMuxIdentity UIntResizeRoundtrip.
From Coq Require Import ZArith List Lia.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From nbits Require Import NBits.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Definition rfa_reset_word_16 inputs path := proj1_sig (formal_symbolic_inputs inputs path (validif_source_address (validif_raw_address nil 8627 0 nil)) nil 32).
Lemma rfa_reset_word_16_size inputs path : size (rfa_reset_word_16 inputs path) = 32%nat.
Proof. exact (proj2_sig (formal_symbolic_inputs inputs path (validif_source_address (validif_raw_address nil 8627 0 nil)) nil 32)). Qed.
Definition rfa_node_8121_expr := (@Evalidif VarOrder.T (@Econst VarOrder.T (Fuint 1) [::false]) (@Econst VarOrder.T (Fuint 32) [::false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false])).
Definition rfa_node_8121_tail := match straight_drop 8628 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma rfa_node_8121_position : straight_drop 8627 flat_statements = Some (@Qcons VarOrder.T (@Snode VarOrder.T 8121 rfa_node_8121_expr) rfa_node_8121_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma rfa_node_8121_safe : formal_typed_suffix_safe flat_memories 8121 rfa_node_8121_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma rfa_node_8121_nonreg : has_register 8121 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem rfa_reset_step_8121 inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 VM.find 8121 result = Some (Gval (Fuint 32) (rfa_reset_word_16 inputs path)).
Proof.
 intros Step.
 eapply formal_combinational_known_node;
 [exact rfa_node_8121_position|exact rfa_node_8121_safe|exact rfa_node_8121_nonreg| |reflexivity|exact Step].
 reflexivity.
Qed.
Theorem rfa_reset_history_8121 inputs path history limit :
 (forall t, (t < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history t) false (history t) flat_statements = Some (history (S t))) ->
 forall t, (1 <= t)%coq_nat -> (t <= limit)%coq_nat ->
 VM.find 8121 (history t) = Some (Gval (Fuint 32) (rfa_reset_word_16 inputs path)).
Proof.
 intros Steps t Lower Upper. destruct t as [|t]; [lia|].
 apply (rfa_reset_step_8121 inputs path (history t) (history t) (history (S t))).
 apply Steps;lia.
Qed.
Definition rfa_node_8122_expr := joint_update_expr_8122.
Theorem rfa_reset_step_8122 inputs path old current result :
 VM.find 8121 old = Some (Gval (Fuint 32) (rfa_reset_word_16 inputs path)) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 VM.find 8122 result = Some (Gval (Fuint 32) (rfa_reset_word_16 inputs path)).
Proof.
 intros Source Step.
 assert (Member : List.In (8122,joint_update_expr_8122) joint_update_expected_nodes).
 { apply (List.nth_error_In joint_update_expected_nodes 1009%nat). vm_compute. reflexivity. }
 destruct (selected_node_safe_position flat_memories flat_statements joint_update_node_offsets flat_statements joint_update_expected_nodes 8122 joint_update_expr_8122 joint_update_node_positions joint_update_node_safety Member) as [count [tail [Position [Safe Nonreg]]]].
 eapply formal_combinational_known_node; [exact Position|exact Safe|exact Nonreg| |reflexivity|exact Step].
 cbn [rfa_node_8122_expr eval_hfexpr_validif_policy eval_href_validif_policy]. exact Source.
Qed.
Theorem rfa_reset_history_8122 inputs path history limit :
 (forall t, (t < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history t) false (history t) flat_statements = Some (history (S t))) ->
 forall t, (2 <= t)%coq_nat -> (t <= limit)%coq_nat ->
 VM.find 8122 (history t) = Some (Gval (Fuint 32) (rfa_reset_word_16 inputs path)).
Proof.
 intros Steps t Lower Upper. destruct t as [|t]; [lia|].
 apply (rfa_reset_step_8122 inputs path (history t) (history t) (history (S t))).
 - apply (rfa_reset_history_8121 inputs path history limit Steps t);lia.
 - apply Steps;lia.
Qed.
Lemma joint_update_connection_803_nonreg : has_register 803 flat_statements = false.
Proof. exact joint_update_connection_803_nonregister. Qed.
Theorem rfa_reset_step_803 inputs path old current result :
 VM.find 8122 old = Some (Gval (Fuint 32) (rfa_reset_word_16 inputs path)) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 VM.find 803 result = Some (Gval (Fuint 32) (rfa_reset_word_16 inputs path)).
Proof.
 intros Source Step.
 apply (declared_connection_value 812 flat_statements joint_update_connection_803_decl joint_update_connection_803_mid joint_update_connection_803_tail 803 8122 32
 (Gval (Fuint 32) (rfa_reset_word_16 inputs path)) (Gval (Fuint 32) (rfa_reset_word_16 inputs path))
 (formal_invalid_policy inputs path) flat_memories old current result joint_update_connection_803_position joint_update_connection_803_split joint_update_connection_803_straight joint_update_connection_803_mid_safe joint_update_connection_803_tail_safe joint_update_connection_803_nonreg (Logic.eq_refl _) Source).
 - assert (Take : take 32 (rfa_reset_word_16 inputs path) = rfa_reset_word_16 inputs path).
   { apply take_oversize. rewrite rfa_reset_word_16_size. reflexivity. }
   cbn [adapt_hvalue_as_type]. rewrite Take. unfold zext_to,zext. rewrite rfa_reset_word_16_size subnn cats0. reflexivity.
 - exact Step.
Qed.
Theorem rfa_reset_history_803 inputs path history limit :
 (forall t, (t < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history t) false (history t) flat_statements = Some (history (S t))) ->
 forall t, (3 <= t)%coq_nat -> (t <= limit)%coq_nat ->
 VM.find 803 (history t) = Some (Gval (Fuint 32) (rfa_reset_word_16 inputs path)).
Proof.
 intros Steps t Lower Upper. destruct t as [|t]; [lia|].
 apply (rfa_reset_step_803 inputs path (history t) (history t) (history (S t))).
 - apply (rfa_reset_history_8122 inputs path history limit Steps t);lia.
 - apply Steps;lia.
Qed.
Definition rfa_node_1101_expr := joint_update_expr_1101.
Theorem rfa_reset_step_1101 inputs path old current result :
 VM.find 803 old = Some (Gval (Fuint 32) (rfa_reset_word_16 inputs path)) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 VM.find 1101 result = Some (Gval (Fuint 32) (rfa_reset_word_16 inputs path)).
Proof.
 intros Source Step.
 assert (Member : List.In (1101,joint_update_expr_1101) joint_update_expected_nodes).
 { apply (List.nth_error_In joint_update_expected_nodes 691%nat). vm_compute. reflexivity. }
 destruct (selected_node_safe_position flat_memories flat_statements joint_update_node_offsets flat_statements joint_update_expected_nodes 1101 joint_update_expr_1101 joint_update_node_positions joint_update_node_safety Member) as [count [tail [Position [Safe Nonreg]]]].
 eapply formal_combinational_known_node; [exact Position|exact Safe|exact Nonreg| |reflexivity|exact Step].
 cbn [rfa_node_1101_expr eval_hfexpr_validif_policy eval_href_validif_policy]. exact Source.
Qed.
Theorem rfa_reset_history_1101 inputs path history limit :
 (forall t, (t < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history t) false (history t) flat_statements = Some (history (S t))) ->
 forall t, (4 <= t)%coq_nat -> (t <= limit)%coq_nat ->
 VM.find 1101 (history t) = Some (Gval (Fuint 32) (rfa_reset_word_16 inputs path)).
Proof.
 intros Steps t Lower Upper. destruct t as [|t]; [lia|].
 apply (rfa_reset_step_1101 inputs path (history t) (history t) (history (S t))).
 - apply (rfa_reset_history_803 inputs path history limit Steps t);lia.
 - apply Steps;lia.
Qed.
Definition rfa_wire_1498_decl := match straight_drop 1578 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition rfa_wire_1498_tail := match straight_drop 8987 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition rfa_wire_1498_mid := take_statements 7408 rfa_wire_1498_decl.
Lemma rfa_wire_1498_position : straight_drop 1577 flat_statements = Some (@Qcons VarOrder.T (@Swire VarOrder.T 1498 (Gtyp (Fuint 32))) rfa_wire_1498_decl).
Proof. vm_compute. reflexivity. Qed.
Lemma rfa_wire_1498_split : rfa_wire_1498_decl = statement_append rfa_wire_1498_mid (@Qcons VarOrder.T (@Sfcnct VarOrder.T (@Eid VarOrder.T 1498) (@Eref VarOrder.T (@Eid VarOrder.T 8122))) rfa_wire_1498_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma rfa_wire_1498_straight : straight_statements rfa_wire_1498_mid.
Proof. vm_compute. exact I. Qed.
Lemma rfa_wire_1498_mid_safe : formal_typed_suffix_safe flat_memories 1498 rfa_wire_1498_mid.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma rfa_wire_1498_tail_safe : formal_typed_suffix_safe flat_memories 1498 rfa_wire_1498_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma rfa_wire_1498_nonreg : has_register 1498 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem rfa_reset_step_1498 inputs path old current result :
 VM.find 8122 old = Some (Gval (Fuint 32) (rfa_reset_word_16 inputs path)) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 VM.find 1498 result = Some (Gval (Fuint 32) (rfa_reset_word_16 inputs path)).
Proof.
 intros Source Step.
 apply (declared_connection_value 1577 flat_statements rfa_wire_1498_decl rfa_wire_1498_mid rfa_wire_1498_tail 1498 8122 32
 (Gval (Fuint 32) (rfa_reset_word_16 inputs path)) (Gval (Fuint 32) (rfa_reset_word_16 inputs path))
 (formal_invalid_policy inputs path) flat_memories old current result rfa_wire_1498_position rfa_wire_1498_split rfa_wire_1498_straight rfa_wire_1498_mid_safe rfa_wire_1498_tail_safe rfa_wire_1498_nonreg (Logic.eq_refl _) Source).
 - assert (Take : take 32 (rfa_reset_word_16 inputs path) = rfa_reset_word_16 inputs path).
   { apply take_oversize. rewrite rfa_reset_word_16_size. reflexivity. }
   cbn [adapt_hvalue_as_type]. rewrite Take. unfold zext_to,zext. rewrite rfa_reset_word_16_size subnn cats0. reflexivity.
 - exact Step.
Qed.
Theorem rfa_reset_history_1498 inputs path history limit :
 (forall t, (t < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history t) false (history t) flat_statements = Some (history (S t))) ->
 forall t, (3 <= t)%coq_nat -> (t <= limit)%coq_nat ->
 VM.find 1498 (history t) = Some (Gval (Fuint 32) (rfa_reset_word_16 inputs path)).
Proof.
 intros Steps t Lower Upper. destruct t as [|t]; [lia|].
 apply (rfa_reset_step_1498 inputs path (history t) (history t) (history (S t))).
 - apply (rfa_reset_history_8122 inputs path history limit Steps t);lia.
 - apply Steps;lia.
Qed.
Definition rfa_wire_1688_decl := match straight_drop 1768 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition rfa_wire_1688_tail := match straight_drop 8239 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition rfa_wire_1688_mid := take_statements 6470 rfa_wire_1688_decl.
Lemma rfa_wire_1688_position : straight_drop 1767 flat_statements = Some (@Qcons VarOrder.T (@Swire VarOrder.T 1688 (Gtyp (Fuint 32))) rfa_wire_1688_decl).
Proof. vm_compute. reflexivity. Qed.
Lemma rfa_wire_1688_split : rfa_wire_1688_decl = statement_append rfa_wire_1688_mid (@Qcons VarOrder.T (@Sfcnct VarOrder.T (@Eid VarOrder.T 1688) (@Eref VarOrder.T (@Eid VarOrder.T 1498))) rfa_wire_1688_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma rfa_wire_1688_straight : straight_statements rfa_wire_1688_mid.
Proof. vm_compute. exact I. Qed.
Lemma rfa_wire_1688_mid_safe : formal_typed_suffix_safe flat_memories 1688 rfa_wire_1688_mid.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma rfa_wire_1688_tail_safe : formal_typed_suffix_safe flat_memories 1688 rfa_wire_1688_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma rfa_wire_1688_nonreg : has_register 1688 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem rfa_reset_step_1688 inputs path old current result :
 VM.find 1498 old = Some (Gval (Fuint 32) (rfa_reset_word_16 inputs path)) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 VM.find 1688 result = Some (Gval (Fuint 32) (rfa_reset_word_16 inputs path)).
Proof.
 intros Source Step.
 apply (declared_connection_value 1767 flat_statements rfa_wire_1688_decl rfa_wire_1688_mid rfa_wire_1688_tail 1688 1498 32
 (Gval (Fuint 32) (rfa_reset_word_16 inputs path)) (Gval (Fuint 32) (rfa_reset_word_16 inputs path))
 (formal_invalid_policy inputs path) flat_memories old current result rfa_wire_1688_position rfa_wire_1688_split rfa_wire_1688_straight rfa_wire_1688_mid_safe rfa_wire_1688_tail_safe rfa_wire_1688_nonreg (Logic.eq_refl _) Source).
 - assert (Take : take 32 (rfa_reset_word_16 inputs path) = rfa_reset_word_16 inputs path).
   { apply take_oversize. rewrite rfa_reset_word_16_size. reflexivity. }
   cbn [adapt_hvalue_as_type]. rewrite Take. unfold zext_to,zext. rewrite rfa_reset_word_16_size subnn cats0. reflexivity.
 - exact Step.
Qed.
Theorem rfa_reset_history_1688 inputs path history limit :
 (forall t, (t < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history t) false (history t) flat_statements = Some (history (S t))) ->
 forall t, (4 <= t)%coq_nat -> (t <= limit)%coq_nat ->
 VM.find 1688 (history t) = Some (Gval (Fuint 32) (rfa_reset_word_16 inputs path)).
Proof.
 intros Steps t Lower Upper. destruct t as [|t]; [lia|].
 apply (rfa_reset_step_1688 inputs path (history t) (history t) (history (S t))).
 - apply (rfa_reset_history_1498 inputs path history limit Steps t);lia.
 - apply Steps;lia.
Qed.
Definition rfa_node_7401_expr := (@Eref VarOrder.T (@Eid VarOrder.T 1688)).
Definition rfa_node_7401_tail := match straight_drop 7573 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma rfa_node_7401_position : straight_drop 7572 flat_statements = Some (@Qcons VarOrder.T (@Snode VarOrder.T 7401 rfa_node_7401_expr) rfa_node_7401_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma rfa_node_7401_safe : formal_typed_suffix_safe flat_memories 7401 rfa_node_7401_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma rfa_node_7401_nonreg : has_register 7401 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem rfa_reset_step_7401 inputs path old current result :
 VM.find 1688 old = Some (Gval (Fuint 32) (rfa_reset_word_16 inputs path)) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 VM.find 7401 result = Some (Gval (Fuint 32) (rfa_reset_word_16 inputs path)).
Proof.
 intros Source Step.
 eapply formal_combinational_known_node;
 [exact rfa_node_7401_position|exact rfa_node_7401_safe|exact rfa_node_7401_nonreg| |reflexivity|exact Step].
 cbn [rfa_node_7401_expr eval_hfexpr_validif_policy eval_href_validif_policy]. exact Source.
Qed.
Theorem rfa_reset_history_7401 inputs path history limit :
 (forall t, (t < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history t) false (history t) flat_statements = Some (history (S t))) ->
 forall t, (5 <= t)%coq_nat -> (t <= limit)%coq_nat ->
 VM.find 7401 (history t) = Some (Gval (Fuint 32) (rfa_reset_word_16 inputs path)).
Proof.
 intros Steps t Lower Upper. destruct t as [|t]; [lia|].
 apply (rfa_reset_step_7401 inputs path (history t) (history t) (history (S t))).
 - apply (rfa_reset_history_1688 inputs path history limit Steps t);lia.
 - apply Steps;lia.
Qed.
Definition rfa_node_7402_expr := (@Eref VarOrder.T (@Eid VarOrder.T 7401)).
Definition rfa_node_7402_tail := match straight_drop 7574 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma rfa_node_7402_position : straight_drop 7573 flat_statements = Some (@Qcons VarOrder.T (@Snode VarOrder.T 7402 rfa_node_7402_expr) rfa_node_7402_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma rfa_node_7402_safe : formal_typed_suffix_safe flat_memories 7402 rfa_node_7402_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma rfa_node_7402_nonreg : has_register 7402 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem rfa_reset_step_7402 inputs path old current result :
 VM.find 7401 old = Some (Gval (Fuint 32) (rfa_reset_word_16 inputs path)) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 VM.find 7402 result = Some (Gval (Fuint 32) (rfa_reset_word_16 inputs path)).
Proof.
 intros Source Step.
 eapply formal_combinational_known_node;
 [exact rfa_node_7402_position|exact rfa_node_7402_safe|exact rfa_node_7402_nonreg| |reflexivity|exact Step].
 cbn [rfa_node_7402_expr eval_hfexpr_validif_policy eval_href_validif_policy]. exact Source.
Qed.
Theorem rfa_reset_history_7402 inputs path history limit :
 (forall t, (t < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history t) false (history t) flat_statements = Some (history (S t))) ->
 forall t, (6 <= t)%coq_nat -> (t <= limit)%coq_nat ->
 VM.find 7402 (history t) = Some (Gval (Fuint 32) (rfa_reset_word_16 inputs path)).
Proof.
 intros Steps t Lower Upper. destruct t as [|t]; [lia|].
 apply (rfa_reset_step_7402 inputs path (history t) (history t) (history (S t))).
 - apply (rfa_reset_history_7401 inputs path history limit Steps t);lia.
 - apply Steps;lia.
Qed.
Definition rfa_reset_word_17 inputs path := proj1_sig (formal_symbolic_inputs inputs path (validif_source_address (validif_raw_address nil 8629 0 nil)) nil 32).
Lemma rfa_reset_word_17_size inputs path : size (rfa_reset_word_17 inputs path) = 32%nat.
Proof. exact (proj2_sig (formal_symbolic_inputs inputs path (validif_source_address (validif_raw_address nil 8629 0 nil)) nil 32)). Qed.
Definition rfa_node_8123_expr := (@Evalidif VarOrder.T (@Econst VarOrder.T (Fuint 1) [::false]) (@Econst VarOrder.T (Fuint 32) [::false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false])).
Definition rfa_node_8123_tail := match straight_drop 8630 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma rfa_node_8123_position : straight_drop 8629 flat_statements = Some (@Qcons VarOrder.T (@Snode VarOrder.T 8123 rfa_node_8123_expr) rfa_node_8123_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma rfa_node_8123_safe : formal_typed_suffix_safe flat_memories 8123 rfa_node_8123_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma rfa_node_8123_nonreg : has_register 8123 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem rfa_reset_step_8123 inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 VM.find 8123 result = Some (Gval (Fuint 32) (rfa_reset_word_17 inputs path)).
Proof.
 intros Step.
 eapply formal_combinational_known_node;
 [exact rfa_node_8123_position|exact rfa_node_8123_safe|exact rfa_node_8123_nonreg| |reflexivity|exact Step].
 reflexivity.
Qed.
Theorem rfa_reset_history_8123 inputs path history limit :
 (forall t, (t < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history t) false (history t) flat_statements = Some (history (S t))) ->
 forall t, (1 <= t)%coq_nat -> (t <= limit)%coq_nat ->
 VM.find 8123 (history t) = Some (Gval (Fuint 32) (rfa_reset_word_17 inputs path)).
Proof.
 intros Steps t Lower Upper. destruct t as [|t]; [lia|].
 apply (rfa_reset_step_8123 inputs path (history t) (history t) (history (S t))).
 apply Steps;lia.
Qed.
Definition rfa_node_8124_expr := joint_update_expr_8124.
Theorem rfa_reset_step_8124 inputs path old current result :
 VM.find 8123 old = Some (Gval (Fuint 32) (rfa_reset_word_17 inputs path)) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 VM.find 8124 result = Some (Gval (Fuint 32) (rfa_reset_word_17 inputs path)).
Proof.
 intros Source Step.
 assert (Member : List.In (8124,joint_update_expr_8124) joint_update_expected_nodes).
 { apply (List.nth_error_In joint_update_expected_nodes 1011%nat). vm_compute. reflexivity. }
 destruct (selected_node_safe_position flat_memories flat_statements joint_update_node_offsets flat_statements joint_update_expected_nodes 8124 joint_update_expr_8124 joint_update_node_positions joint_update_node_safety Member) as [count [tail [Position [Safe Nonreg]]]].
 eapply formal_combinational_known_node; [exact Position|exact Safe|exact Nonreg| |reflexivity|exact Step].
 cbn [rfa_node_8124_expr eval_hfexpr_validif_policy eval_href_validif_policy]. exact Source.
Qed.
Theorem rfa_reset_history_8124 inputs path history limit :
 (forall t, (t < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history t) false (history t) flat_statements = Some (history (S t))) ->
 forall t, (2 <= t)%coq_nat -> (t <= limit)%coq_nat ->
 VM.find 8124 (history t) = Some (Gval (Fuint 32) (rfa_reset_word_17 inputs path)).
Proof.
 intros Steps t Lower Upper. destruct t as [|t]; [lia|].
 apply (rfa_reset_step_8124 inputs path (history t) (history t) (history (S t))).
 - apply (rfa_reset_history_8123 inputs path history limit Steps t);lia.
 - apply Steps;lia.
Qed.
Lemma joint_update_connection_804_nonreg : has_register 804 flat_statements = false.
Proof. exact joint_update_connection_804_nonregister. Qed.
Theorem rfa_reset_step_804 inputs path old current result :
 VM.find 8124 old = Some (Gval (Fuint 32) (rfa_reset_word_17 inputs path)) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 VM.find 804 result = Some (Gval (Fuint 32) (rfa_reset_word_17 inputs path)).
Proof.
 intros Source Step.
 apply (declared_connection_value 813 flat_statements joint_update_connection_804_decl joint_update_connection_804_mid joint_update_connection_804_tail 804 8124 32
 (Gval (Fuint 32) (rfa_reset_word_17 inputs path)) (Gval (Fuint 32) (rfa_reset_word_17 inputs path))
 (formal_invalid_policy inputs path) flat_memories old current result joint_update_connection_804_position joint_update_connection_804_split joint_update_connection_804_straight joint_update_connection_804_mid_safe joint_update_connection_804_tail_safe joint_update_connection_804_nonreg (Logic.eq_refl _) Source).
 - assert (Take : take 32 (rfa_reset_word_17 inputs path) = rfa_reset_word_17 inputs path).
   { apply take_oversize. rewrite rfa_reset_word_17_size. reflexivity. }
   cbn [adapt_hvalue_as_type]. rewrite Take. unfold zext_to,zext. rewrite rfa_reset_word_17_size subnn cats0. reflexivity.
 - exact Step.
Qed.
Theorem rfa_reset_history_804 inputs path history limit :
 (forall t, (t < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history t) false (history t) flat_statements = Some (history (S t))) ->
 forall t, (3 <= t)%coq_nat -> (t <= limit)%coq_nat ->
 VM.find 804 (history t) = Some (Gval (Fuint 32) (rfa_reset_word_17 inputs path)).
Proof.
 intros Steps t Lower Upper. destruct t as [|t]; [lia|].
 apply (rfa_reset_step_804 inputs path (history t) (history t) (history (S t))).
 - apply (rfa_reset_history_8124 inputs path history limit Steps t);lia.
 - apply Steps;lia.
Qed.
Definition rfa_node_1102_expr := joint_update_expr_1102.
Theorem rfa_reset_step_1102 inputs path old current result :
 VM.find 804 old = Some (Gval (Fuint 32) (rfa_reset_word_17 inputs path)) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 VM.find 1102 result = Some (Gval (Fuint 32) (rfa_reset_word_17 inputs path)).
Proof.
 intros Source Step.
 assert (Member : List.In (1102,joint_update_expr_1102) joint_update_expected_nodes).
 { apply (List.nth_error_In joint_update_expected_nodes 692%nat). vm_compute. reflexivity. }
 destruct (selected_node_safe_position flat_memories flat_statements joint_update_node_offsets flat_statements joint_update_expected_nodes 1102 joint_update_expr_1102 joint_update_node_positions joint_update_node_safety Member) as [count [tail [Position [Safe Nonreg]]]].
 eapply formal_combinational_known_node; [exact Position|exact Safe|exact Nonreg| |reflexivity|exact Step].
 cbn [rfa_node_1102_expr eval_hfexpr_validif_policy eval_href_validif_policy]. exact Source.
Qed.
Theorem rfa_reset_history_1102 inputs path history limit :
 (forall t, (t < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history t) false (history t) flat_statements = Some (history (S t))) ->
 forall t, (4 <= t)%coq_nat -> (t <= limit)%coq_nat ->
 VM.find 1102 (history t) = Some (Gval (Fuint 32) (rfa_reset_word_17 inputs path)).
Proof.
 intros Steps t Lower Upper. destruct t as [|t]; [lia|].
 apply (rfa_reset_step_1102 inputs path (history t) (history t) (history (S t))).
 - apply (rfa_reset_history_804 inputs path history limit Steps t);lia.
 - apply Steps;lia.
Qed.
Definition rfa_wire_1499_decl := match straight_drop 1579 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition rfa_wire_1499_tail := match straight_drop 8988 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition rfa_wire_1499_mid := take_statements 7408 rfa_wire_1499_decl.
Lemma rfa_wire_1499_position : straight_drop 1578 flat_statements = Some (@Qcons VarOrder.T (@Swire VarOrder.T 1499 (Gtyp (Fuint 32))) rfa_wire_1499_decl).
Proof. vm_compute. reflexivity. Qed.
Lemma rfa_wire_1499_split : rfa_wire_1499_decl = statement_append rfa_wire_1499_mid (@Qcons VarOrder.T (@Sfcnct VarOrder.T (@Eid VarOrder.T 1499) (@Eref VarOrder.T (@Eid VarOrder.T 8124))) rfa_wire_1499_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma rfa_wire_1499_straight : straight_statements rfa_wire_1499_mid.
Proof. vm_compute. exact I. Qed.
Lemma rfa_wire_1499_mid_safe : formal_typed_suffix_safe flat_memories 1499 rfa_wire_1499_mid.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma rfa_wire_1499_tail_safe : formal_typed_suffix_safe flat_memories 1499 rfa_wire_1499_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma rfa_wire_1499_nonreg : has_register 1499 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem rfa_reset_step_1499 inputs path old current result :
 VM.find 8124 old = Some (Gval (Fuint 32) (rfa_reset_word_17 inputs path)) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 VM.find 1499 result = Some (Gval (Fuint 32) (rfa_reset_word_17 inputs path)).
Proof.
 intros Source Step.
 apply (declared_connection_value 1578 flat_statements rfa_wire_1499_decl rfa_wire_1499_mid rfa_wire_1499_tail 1499 8124 32
 (Gval (Fuint 32) (rfa_reset_word_17 inputs path)) (Gval (Fuint 32) (rfa_reset_word_17 inputs path))
 (formal_invalid_policy inputs path) flat_memories old current result rfa_wire_1499_position rfa_wire_1499_split rfa_wire_1499_straight rfa_wire_1499_mid_safe rfa_wire_1499_tail_safe rfa_wire_1499_nonreg (Logic.eq_refl _) Source).
 - assert (Take : take 32 (rfa_reset_word_17 inputs path) = rfa_reset_word_17 inputs path).
   { apply take_oversize. rewrite rfa_reset_word_17_size. reflexivity. }
   cbn [adapt_hvalue_as_type]. rewrite Take. unfold zext_to,zext. rewrite rfa_reset_word_17_size subnn cats0. reflexivity.
 - exact Step.
Qed.
Theorem rfa_reset_history_1499 inputs path history limit :
 (forall t, (t < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history t) false (history t) flat_statements = Some (history (S t))) ->
 forall t, (3 <= t)%coq_nat -> (t <= limit)%coq_nat ->
 VM.find 1499 (history t) = Some (Gval (Fuint 32) (rfa_reset_word_17 inputs path)).
Proof.
 intros Steps t Lower Upper. destruct t as [|t]; [lia|].
 apply (rfa_reset_step_1499 inputs path (history t) (history t) (history (S t))).
 - apply (rfa_reset_history_8124 inputs path history limit Steps t);lia.
 - apply Steps;lia.
Qed.
Definition rfa_wire_1689_decl := match straight_drop 1769 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition rfa_wire_1689_tail := match straight_drop 8240 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition rfa_wire_1689_mid := take_statements 6470 rfa_wire_1689_decl.
Lemma rfa_wire_1689_position : straight_drop 1768 flat_statements = Some (@Qcons VarOrder.T (@Swire VarOrder.T 1689 (Gtyp (Fuint 32))) rfa_wire_1689_decl).
Proof. vm_compute. reflexivity. Qed.
Lemma rfa_wire_1689_split : rfa_wire_1689_decl = statement_append rfa_wire_1689_mid (@Qcons VarOrder.T (@Sfcnct VarOrder.T (@Eid VarOrder.T 1689) (@Eref VarOrder.T (@Eid VarOrder.T 1499))) rfa_wire_1689_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma rfa_wire_1689_straight : straight_statements rfa_wire_1689_mid.
Proof. vm_compute. exact I. Qed.
Lemma rfa_wire_1689_mid_safe : formal_typed_suffix_safe flat_memories 1689 rfa_wire_1689_mid.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma rfa_wire_1689_tail_safe : formal_typed_suffix_safe flat_memories 1689 rfa_wire_1689_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma rfa_wire_1689_nonreg : has_register 1689 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem rfa_reset_step_1689 inputs path old current result :
 VM.find 1499 old = Some (Gval (Fuint 32) (rfa_reset_word_17 inputs path)) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 VM.find 1689 result = Some (Gval (Fuint 32) (rfa_reset_word_17 inputs path)).
Proof.
 intros Source Step.
 apply (declared_connection_value 1768 flat_statements rfa_wire_1689_decl rfa_wire_1689_mid rfa_wire_1689_tail 1689 1499 32
 (Gval (Fuint 32) (rfa_reset_word_17 inputs path)) (Gval (Fuint 32) (rfa_reset_word_17 inputs path))
 (formal_invalid_policy inputs path) flat_memories old current result rfa_wire_1689_position rfa_wire_1689_split rfa_wire_1689_straight rfa_wire_1689_mid_safe rfa_wire_1689_tail_safe rfa_wire_1689_nonreg (Logic.eq_refl _) Source).
 - assert (Take : take 32 (rfa_reset_word_17 inputs path) = rfa_reset_word_17 inputs path).
   { apply take_oversize. rewrite rfa_reset_word_17_size. reflexivity. }
   cbn [adapt_hvalue_as_type]. rewrite Take. unfold zext_to,zext. rewrite rfa_reset_word_17_size subnn cats0. reflexivity.
 - exact Step.
Qed.
Theorem rfa_reset_history_1689 inputs path history limit :
 (forall t, (t < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history t) false (history t) flat_statements = Some (history (S t))) ->
 forall t, (4 <= t)%coq_nat -> (t <= limit)%coq_nat ->
 VM.find 1689 (history t) = Some (Gval (Fuint 32) (rfa_reset_word_17 inputs path)).
Proof.
 intros Steps t Lower Upper. destruct t as [|t]; [lia|].
 apply (rfa_reset_step_1689 inputs path (history t) (history t) (history (S t))).
 - apply (rfa_reset_history_1499 inputs path history limit Steps t);lia.
 - apply Steps;lia.
Qed.
Definition rfa_node_7403_expr := (@Eref VarOrder.T (@Eid VarOrder.T 1689)).
Definition rfa_node_7403_tail := match straight_drop 7575 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma rfa_node_7403_position : straight_drop 7574 flat_statements = Some (@Qcons VarOrder.T (@Snode VarOrder.T 7403 rfa_node_7403_expr) rfa_node_7403_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma rfa_node_7403_safe : formal_typed_suffix_safe flat_memories 7403 rfa_node_7403_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma rfa_node_7403_nonreg : has_register 7403 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem rfa_reset_step_7403 inputs path old current result :
 VM.find 1689 old = Some (Gval (Fuint 32) (rfa_reset_word_17 inputs path)) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 VM.find 7403 result = Some (Gval (Fuint 32) (rfa_reset_word_17 inputs path)).
Proof.
 intros Source Step.
 eapply formal_combinational_known_node;
 [exact rfa_node_7403_position|exact rfa_node_7403_safe|exact rfa_node_7403_nonreg| |reflexivity|exact Step].
 cbn [rfa_node_7403_expr eval_hfexpr_validif_policy eval_href_validif_policy]. exact Source.
Qed.
Theorem rfa_reset_history_7403 inputs path history limit :
 (forall t, (t < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history t) false (history t) flat_statements = Some (history (S t))) ->
 forall t, (5 <= t)%coq_nat -> (t <= limit)%coq_nat ->
 VM.find 7403 (history t) = Some (Gval (Fuint 32) (rfa_reset_word_17 inputs path)).
Proof.
 intros Steps t Lower Upper. destruct t as [|t]; [lia|].
 apply (rfa_reset_step_7403 inputs path (history t) (history t) (history (S t))).
 - apply (rfa_reset_history_1689 inputs path history limit Steps t);lia.
 - apply Steps;lia.
Qed.
Definition rfa_node_7404_expr := (@Eref VarOrder.T (@Eid VarOrder.T 7403)).
Definition rfa_node_7404_tail := match straight_drop 7576 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma rfa_node_7404_position : straight_drop 7575 flat_statements = Some (@Qcons VarOrder.T (@Snode VarOrder.T 7404 rfa_node_7404_expr) rfa_node_7404_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma rfa_node_7404_safe : formal_typed_suffix_safe flat_memories 7404 rfa_node_7404_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma rfa_node_7404_nonreg : has_register 7404 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem rfa_reset_step_7404 inputs path old current result :
 VM.find 7403 old = Some (Gval (Fuint 32) (rfa_reset_word_17 inputs path)) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 VM.find 7404 result = Some (Gval (Fuint 32) (rfa_reset_word_17 inputs path)).
Proof.
 intros Source Step.
 eapply formal_combinational_known_node;
 [exact rfa_node_7404_position|exact rfa_node_7404_safe|exact rfa_node_7404_nonreg| |reflexivity|exact Step].
 cbn [rfa_node_7404_expr eval_hfexpr_validif_policy eval_href_validif_policy]. exact Source.
Qed.
Theorem rfa_reset_history_7404 inputs path history limit :
 (forall t, (t < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history t) false (history t) flat_statements = Some (history (S t))) ->
 forall t, (6 <= t)%coq_nat -> (t <= limit)%coq_nat ->
 VM.find 7404 (history t) = Some (Gval (Fuint 32) (rfa_reset_word_17 inputs path)).
Proof.
 intros Steps t Lower Upper. destruct t as [|t]; [lia|].
 apply (rfa_reset_step_7404 inputs path (history t) (history t) (history (S t))).
 - apply (rfa_reset_history_7403 inputs path history limit Steps t);lia.
 - apply Steps;lia.
Qed.
Definition rfa_reset_word_18 inputs path := proj1_sig (formal_symbolic_inputs inputs path (validif_source_address (validif_raw_address nil 8631 0 nil)) nil 32).
Lemma rfa_reset_word_18_size inputs path : size (rfa_reset_word_18 inputs path) = 32%nat.
Proof. exact (proj2_sig (formal_symbolic_inputs inputs path (validif_source_address (validif_raw_address nil 8631 0 nil)) nil 32)). Qed.
Definition rfa_node_8125_expr := (@Evalidif VarOrder.T (@Econst VarOrder.T (Fuint 1) [::false]) (@Econst VarOrder.T (Fuint 32) [::false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false])).
Definition rfa_node_8125_tail := match straight_drop 8632 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma rfa_node_8125_position : straight_drop 8631 flat_statements = Some (@Qcons VarOrder.T (@Snode VarOrder.T 8125 rfa_node_8125_expr) rfa_node_8125_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma rfa_node_8125_safe : formal_typed_suffix_safe flat_memories 8125 rfa_node_8125_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma rfa_node_8125_nonreg : has_register 8125 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem rfa_reset_step_8125 inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 VM.find 8125 result = Some (Gval (Fuint 32) (rfa_reset_word_18 inputs path)).
Proof.
 intros Step.
 eapply formal_combinational_known_node;
 [exact rfa_node_8125_position|exact rfa_node_8125_safe|exact rfa_node_8125_nonreg| |reflexivity|exact Step].
 reflexivity.
Qed.
Theorem rfa_reset_history_8125 inputs path history limit :
 (forall t, (t < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history t) false (history t) flat_statements = Some (history (S t))) ->
 forall t, (1 <= t)%coq_nat -> (t <= limit)%coq_nat ->
 VM.find 8125 (history t) = Some (Gval (Fuint 32) (rfa_reset_word_18 inputs path)).
Proof.
 intros Steps t Lower Upper. destruct t as [|t]; [lia|].
 apply (rfa_reset_step_8125 inputs path (history t) (history t) (history (S t))).
 apply Steps;lia.
Qed.
Definition rfa_node_8126_expr := joint_update_expr_8126.
Theorem rfa_reset_step_8126 inputs path old current result :
 VM.find 8125 old = Some (Gval (Fuint 32) (rfa_reset_word_18 inputs path)) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 VM.find 8126 result = Some (Gval (Fuint 32) (rfa_reset_word_18 inputs path)).
Proof.
 intros Source Step.
 assert (Member : List.In (8126,joint_update_expr_8126) joint_update_expected_nodes).
 { apply (List.nth_error_In joint_update_expected_nodes 1013%nat). vm_compute. reflexivity. }
 destruct (selected_node_safe_position flat_memories flat_statements joint_update_node_offsets flat_statements joint_update_expected_nodes 8126 joint_update_expr_8126 joint_update_node_positions joint_update_node_safety Member) as [count [tail [Position [Safe Nonreg]]]].
 eapply formal_combinational_known_node; [exact Position|exact Safe|exact Nonreg| |reflexivity|exact Step].
 cbn [rfa_node_8126_expr eval_hfexpr_validif_policy eval_href_validif_policy]. exact Source.
Qed.
Theorem rfa_reset_history_8126 inputs path history limit :
 (forall t, (t < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history t) false (history t) flat_statements = Some (history (S t))) ->
 forall t, (2 <= t)%coq_nat -> (t <= limit)%coq_nat ->
 VM.find 8126 (history t) = Some (Gval (Fuint 32) (rfa_reset_word_18 inputs path)).
Proof.
 intros Steps t Lower Upper. destruct t as [|t]; [lia|].
 apply (rfa_reset_step_8126 inputs path (history t) (history t) (history (S t))).
 - apply (rfa_reset_history_8125 inputs path history limit Steps t);lia.
 - apply Steps;lia.
Qed.
Lemma joint_update_connection_805_nonreg : has_register 805 flat_statements = false.
Proof. exact joint_update_connection_805_nonregister. Qed.
Theorem rfa_reset_step_805 inputs path old current result :
 VM.find 8126 old = Some (Gval (Fuint 32) (rfa_reset_word_18 inputs path)) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 VM.find 805 result = Some (Gval (Fuint 32) (rfa_reset_word_18 inputs path)).
Proof.
 intros Source Step.
 apply (declared_connection_value 814 flat_statements joint_update_connection_805_decl joint_update_connection_805_mid joint_update_connection_805_tail 805 8126 32
 (Gval (Fuint 32) (rfa_reset_word_18 inputs path)) (Gval (Fuint 32) (rfa_reset_word_18 inputs path))
 (formal_invalid_policy inputs path) flat_memories old current result joint_update_connection_805_position joint_update_connection_805_split joint_update_connection_805_straight joint_update_connection_805_mid_safe joint_update_connection_805_tail_safe joint_update_connection_805_nonreg (Logic.eq_refl _) Source).
 - assert (Take : take 32 (rfa_reset_word_18 inputs path) = rfa_reset_word_18 inputs path).
   { apply take_oversize. rewrite rfa_reset_word_18_size. reflexivity. }
   cbn [adapt_hvalue_as_type]. rewrite Take. unfold zext_to,zext. rewrite rfa_reset_word_18_size subnn cats0. reflexivity.
 - exact Step.
Qed.
Theorem rfa_reset_history_805 inputs path history limit :
 (forall t, (t < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history t) false (history t) flat_statements = Some (history (S t))) ->
 forall t, (3 <= t)%coq_nat -> (t <= limit)%coq_nat ->
 VM.find 805 (history t) = Some (Gval (Fuint 32) (rfa_reset_word_18 inputs path)).
Proof.
 intros Steps t Lower Upper. destruct t as [|t]; [lia|].
 apply (rfa_reset_step_805 inputs path (history t) (history t) (history (S t))).
 - apply (rfa_reset_history_8126 inputs path history limit Steps t);lia.
 - apply Steps;lia.
Qed.
Definition rfa_node_1103_expr := joint_update_expr_1103.
Theorem rfa_reset_step_1103 inputs path old current result :
 VM.find 805 old = Some (Gval (Fuint 32) (rfa_reset_word_18 inputs path)) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 VM.find 1103 result = Some (Gval (Fuint 32) (rfa_reset_word_18 inputs path)).
Proof.
 intros Source Step.
 assert (Member : List.In (1103,joint_update_expr_1103) joint_update_expected_nodes).
 { apply (List.nth_error_In joint_update_expected_nodes 693%nat). vm_compute. reflexivity. }
 destruct (selected_node_safe_position flat_memories flat_statements joint_update_node_offsets flat_statements joint_update_expected_nodes 1103 joint_update_expr_1103 joint_update_node_positions joint_update_node_safety Member) as [count [tail [Position [Safe Nonreg]]]].
 eapply formal_combinational_known_node; [exact Position|exact Safe|exact Nonreg| |reflexivity|exact Step].
 cbn [rfa_node_1103_expr eval_hfexpr_validif_policy eval_href_validif_policy]. exact Source.
Qed.
Theorem rfa_reset_history_1103 inputs path history limit :
 (forall t, (t < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history t) false (history t) flat_statements = Some (history (S t))) ->
 forall t, (4 <= t)%coq_nat -> (t <= limit)%coq_nat ->
 VM.find 1103 (history t) = Some (Gval (Fuint 32) (rfa_reset_word_18 inputs path)).
Proof.
 intros Steps t Lower Upper. destruct t as [|t]; [lia|].
 apply (rfa_reset_step_1103 inputs path (history t) (history t) (history (S t))).
 - apply (rfa_reset_history_805 inputs path history limit Steps t);lia.
 - apply Steps;lia.
Qed.
Definition rfa_wire_1500_decl := match straight_drop 1580 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition rfa_wire_1500_tail := match straight_drop 8989 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition rfa_wire_1500_mid := take_statements 7408 rfa_wire_1500_decl.
Lemma rfa_wire_1500_position : straight_drop 1579 flat_statements = Some (@Qcons VarOrder.T (@Swire VarOrder.T 1500 (Gtyp (Fuint 32))) rfa_wire_1500_decl).
Proof. vm_compute. reflexivity. Qed.
Lemma rfa_wire_1500_split : rfa_wire_1500_decl = statement_append rfa_wire_1500_mid (@Qcons VarOrder.T (@Sfcnct VarOrder.T (@Eid VarOrder.T 1500) (@Eref VarOrder.T (@Eid VarOrder.T 8126))) rfa_wire_1500_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma rfa_wire_1500_straight : straight_statements rfa_wire_1500_mid.
Proof. vm_compute. exact I. Qed.
Lemma rfa_wire_1500_mid_safe : formal_typed_suffix_safe flat_memories 1500 rfa_wire_1500_mid.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma rfa_wire_1500_tail_safe : formal_typed_suffix_safe flat_memories 1500 rfa_wire_1500_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma rfa_wire_1500_nonreg : has_register 1500 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem rfa_reset_step_1500 inputs path old current result :
 VM.find 8126 old = Some (Gval (Fuint 32) (rfa_reset_word_18 inputs path)) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 VM.find 1500 result = Some (Gval (Fuint 32) (rfa_reset_word_18 inputs path)).
Proof.
 intros Source Step.
 apply (declared_connection_value 1579 flat_statements rfa_wire_1500_decl rfa_wire_1500_mid rfa_wire_1500_tail 1500 8126 32
 (Gval (Fuint 32) (rfa_reset_word_18 inputs path)) (Gval (Fuint 32) (rfa_reset_word_18 inputs path))
 (formal_invalid_policy inputs path) flat_memories old current result rfa_wire_1500_position rfa_wire_1500_split rfa_wire_1500_straight rfa_wire_1500_mid_safe rfa_wire_1500_tail_safe rfa_wire_1500_nonreg (Logic.eq_refl _) Source).
 - assert (Take : take 32 (rfa_reset_word_18 inputs path) = rfa_reset_word_18 inputs path).
   { apply take_oversize. rewrite rfa_reset_word_18_size. reflexivity. }
   cbn [adapt_hvalue_as_type]. rewrite Take. unfold zext_to,zext. rewrite rfa_reset_word_18_size subnn cats0. reflexivity.
 - exact Step.
Qed.
Theorem rfa_reset_history_1500 inputs path history limit :
 (forall t, (t < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history t) false (history t) flat_statements = Some (history (S t))) ->
 forall t, (3 <= t)%coq_nat -> (t <= limit)%coq_nat ->
 VM.find 1500 (history t) = Some (Gval (Fuint 32) (rfa_reset_word_18 inputs path)).
Proof.
 intros Steps t Lower Upper. destruct t as [|t]; [lia|].
 apply (rfa_reset_step_1500 inputs path (history t) (history t) (history (S t))).
 - apply (rfa_reset_history_8126 inputs path history limit Steps t);lia.
 - apply Steps;lia.
Qed.
Definition rfa_wire_1690_decl := match straight_drop 1770 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition rfa_wire_1690_tail := match straight_drop 8241 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition rfa_wire_1690_mid := take_statements 6470 rfa_wire_1690_decl.
Lemma rfa_wire_1690_position : straight_drop 1769 flat_statements = Some (@Qcons VarOrder.T (@Swire VarOrder.T 1690 (Gtyp (Fuint 32))) rfa_wire_1690_decl).
Proof. vm_compute. reflexivity. Qed.
Lemma rfa_wire_1690_split : rfa_wire_1690_decl = statement_append rfa_wire_1690_mid (@Qcons VarOrder.T (@Sfcnct VarOrder.T (@Eid VarOrder.T 1690) (@Eref VarOrder.T (@Eid VarOrder.T 1500))) rfa_wire_1690_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma rfa_wire_1690_straight : straight_statements rfa_wire_1690_mid.
Proof. vm_compute. exact I. Qed.
Lemma rfa_wire_1690_mid_safe : formal_typed_suffix_safe flat_memories 1690 rfa_wire_1690_mid.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma rfa_wire_1690_tail_safe : formal_typed_suffix_safe flat_memories 1690 rfa_wire_1690_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma rfa_wire_1690_nonreg : has_register 1690 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem rfa_reset_step_1690 inputs path old current result :
 VM.find 1500 old = Some (Gval (Fuint 32) (rfa_reset_word_18 inputs path)) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 VM.find 1690 result = Some (Gval (Fuint 32) (rfa_reset_word_18 inputs path)).
Proof.
 intros Source Step.
 apply (declared_connection_value 1769 flat_statements rfa_wire_1690_decl rfa_wire_1690_mid rfa_wire_1690_tail 1690 1500 32
 (Gval (Fuint 32) (rfa_reset_word_18 inputs path)) (Gval (Fuint 32) (rfa_reset_word_18 inputs path))
 (formal_invalid_policy inputs path) flat_memories old current result rfa_wire_1690_position rfa_wire_1690_split rfa_wire_1690_straight rfa_wire_1690_mid_safe rfa_wire_1690_tail_safe rfa_wire_1690_nonreg (Logic.eq_refl _) Source).
 - assert (Take : take 32 (rfa_reset_word_18 inputs path) = rfa_reset_word_18 inputs path).
   { apply take_oversize. rewrite rfa_reset_word_18_size. reflexivity. }
   cbn [adapt_hvalue_as_type]. rewrite Take. unfold zext_to,zext. rewrite rfa_reset_word_18_size subnn cats0. reflexivity.
 - exact Step.
Qed.
Theorem rfa_reset_history_1690 inputs path history limit :
 (forall t, (t < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history t) false (history t) flat_statements = Some (history (S t))) ->
 forall t, (4 <= t)%coq_nat -> (t <= limit)%coq_nat ->
 VM.find 1690 (history t) = Some (Gval (Fuint 32) (rfa_reset_word_18 inputs path)).
Proof.
 intros Steps t Lower Upper. destruct t as [|t]; [lia|].
 apply (rfa_reset_step_1690 inputs path (history t) (history t) (history (S t))).
 - apply (rfa_reset_history_1500 inputs path history limit Steps t);lia.
 - apply Steps;lia.
Qed.
Definition rfa_node_7405_expr := (@Eref VarOrder.T (@Eid VarOrder.T 1690)).
Definition rfa_node_7405_tail := match straight_drop 7577 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma rfa_node_7405_position : straight_drop 7576 flat_statements = Some (@Qcons VarOrder.T (@Snode VarOrder.T 7405 rfa_node_7405_expr) rfa_node_7405_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma rfa_node_7405_safe : formal_typed_suffix_safe flat_memories 7405 rfa_node_7405_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma rfa_node_7405_nonreg : has_register 7405 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem rfa_reset_step_7405 inputs path old current result :
 VM.find 1690 old = Some (Gval (Fuint 32) (rfa_reset_word_18 inputs path)) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 VM.find 7405 result = Some (Gval (Fuint 32) (rfa_reset_word_18 inputs path)).
Proof.
 intros Source Step.
 eapply formal_combinational_known_node;
 [exact rfa_node_7405_position|exact rfa_node_7405_safe|exact rfa_node_7405_nonreg| |reflexivity|exact Step].
 cbn [rfa_node_7405_expr eval_hfexpr_validif_policy eval_href_validif_policy]. exact Source.
Qed.
Theorem rfa_reset_history_7405 inputs path history limit :
 (forall t, (t < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history t) false (history t) flat_statements = Some (history (S t))) ->
 forall t, (5 <= t)%coq_nat -> (t <= limit)%coq_nat ->
 VM.find 7405 (history t) = Some (Gval (Fuint 32) (rfa_reset_word_18 inputs path)).
Proof.
 intros Steps t Lower Upper. destruct t as [|t]; [lia|].
 apply (rfa_reset_step_7405 inputs path (history t) (history t) (history (S t))).
 - apply (rfa_reset_history_1690 inputs path history limit Steps t);lia.
 - apply Steps;lia.
Qed.
Definition rfa_node_7406_expr := (@Eref VarOrder.T (@Eid VarOrder.T 7405)).
Definition rfa_node_7406_tail := match straight_drop 7578 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma rfa_node_7406_position : straight_drop 7577 flat_statements = Some (@Qcons VarOrder.T (@Snode VarOrder.T 7406 rfa_node_7406_expr) rfa_node_7406_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma rfa_node_7406_safe : formal_typed_suffix_safe flat_memories 7406 rfa_node_7406_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma rfa_node_7406_nonreg : has_register 7406 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem rfa_reset_step_7406 inputs path old current result :
 VM.find 7405 old = Some (Gval (Fuint 32) (rfa_reset_word_18 inputs path)) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 VM.find 7406 result = Some (Gval (Fuint 32) (rfa_reset_word_18 inputs path)).
Proof.
 intros Source Step.
 eapply formal_combinational_known_node;
 [exact rfa_node_7406_position|exact rfa_node_7406_safe|exact rfa_node_7406_nonreg| |reflexivity|exact Step].
 cbn [rfa_node_7406_expr eval_hfexpr_validif_policy eval_href_validif_policy]. exact Source.
Qed.
Theorem rfa_reset_history_7406 inputs path history limit :
 (forall t, (t < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history t) false (history t) flat_statements = Some (history (S t))) ->
 forall t, (6 <= t)%coq_nat -> (t <= limit)%coq_nat ->
 VM.find 7406 (history t) = Some (Gval (Fuint 32) (rfa_reset_word_18 inputs path)).
Proof.
 intros Steps t Lower Upper. destruct t as [|t]; [lia|].
 apply (rfa_reset_step_7406 inputs path (history t) (history t) (history (S t))).
 - apply (rfa_reset_history_7405 inputs path history limit Steps t);lia.
 - apply Steps;lia.
Qed.
Definition rfa_reset_word_19 inputs path := proj1_sig (formal_symbolic_inputs inputs path (validif_source_address (validif_raw_address nil 8633 0 nil)) nil 32).
Lemma rfa_reset_word_19_size inputs path : size (rfa_reset_word_19 inputs path) = 32%nat.
Proof. exact (proj2_sig (formal_symbolic_inputs inputs path (validif_source_address (validif_raw_address nil 8633 0 nil)) nil 32)). Qed.
Definition rfa_node_8127_expr := (@Evalidif VarOrder.T (@Econst VarOrder.T (Fuint 1) [::false]) (@Econst VarOrder.T (Fuint 32) [::false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false])).
Definition rfa_node_8127_tail := match straight_drop 8634 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma rfa_node_8127_position : straight_drop 8633 flat_statements = Some (@Qcons VarOrder.T (@Snode VarOrder.T 8127 rfa_node_8127_expr) rfa_node_8127_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma rfa_node_8127_safe : formal_typed_suffix_safe flat_memories 8127 rfa_node_8127_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma rfa_node_8127_nonreg : has_register 8127 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem rfa_reset_step_8127 inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 VM.find 8127 result = Some (Gval (Fuint 32) (rfa_reset_word_19 inputs path)).
Proof.
 intros Step.
 eapply formal_combinational_known_node;
 [exact rfa_node_8127_position|exact rfa_node_8127_safe|exact rfa_node_8127_nonreg| |reflexivity|exact Step].
 reflexivity.
Qed.
Theorem rfa_reset_history_8127 inputs path history limit :
 (forall t, (t < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history t) false (history t) flat_statements = Some (history (S t))) ->
 forall t, (1 <= t)%coq_nat -> (t <= limit)%coq_nat ->
 VM.find 8127 (history t) = Some (Gval (Fuint 32) (rfa_reset_word_19 inputs path)).
Proof.
 intros Steps t Lower Upper. destruct t as [|t]; [lia|].
 apply (rfa_reset_step_8127 inputs path (history t) (history t) (history (S t))).
 apply Steps;lia.
Qed.
Definition rfa_node_8128_expr := joint_update_expr_8128.
Theorem rfa_reset_step_8128 inputs path old current result :
 VM.find 8127 old = Some (Gval (Fuint 32) (rfa_reset_word_19 inputs path)) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 VM.find 8128 result = Some (Gval (Fuint 32) (rfa_reset_word_19 inputs path)).
Proof.
 intros Source Step.
 assert (Member : List.In (8128,joint_update_expr_8128) joint_update_expected_nodes).
 { apply (List.nth_error_In joint_update_expected_nodes 1015%nat). vm_compute. reflexivity. }
 destruct (selected_node_safe_position flat_memories flat_statements joint_update_node_offsets flat_statements joint_update_expected_nodes 8128 joint_update_expr_8128 joint_update_node_positions joint_update_node_safety Member) as [count [tail [Position [Safe Nonreg]]]].
 eapply formal_combinational_known_node; [exact Position|exact Safe|exact Nonreg| |reflexivity|exact Step].
 cbn [rfa_node_8128_expr eval_hfexpr_validif_policy eval_href_validif_policy]. exact Source.
Qed.
Theorem rfa_reset_history_8128 inputs path history limit :
 (forall t, (t < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history t) false (history t) flat_statements = Some (history (S t))) ->
 forall t, (2 <= t)%coq_nat -> (t <= limit)%coq_nat ->
 VM.find 8128 (history t) = Some (Gval (Fuint 32) (rfa_reset_word_19 inputs path)).
Proof.
 intros Steps t Lower Upper. destruct t as [|t]; [lia|].
 apply (rfa_reset_step_8128 inputs path (history t) (history t) (history (S t))).
 - apply (rfa_reset_history_8127 inputs path history limit Steps t);lia.
 - apply Steps;lia.
Qed.
Lemma joint_update_connection_806_nonreg : has_register 806 flat_statements = false.
Proof. exact joint_update_connection_806_nonregister. Qed.
Theorem rfa_reset_step_806 inputs path old current result :
 VM.find 8128 old = Some (Gval (Fuint 32) (rfa_reset_word_19 inputs path)) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 VM.find 806 result = Some (Gval (Fuint 32) (rfa_reset_word_19 inputs path)).
Proof.
 intros Source Step.
 apply (declared_connection_value 815 flat_statements joint_update_connection_806_decl joint_update_connection_806_mid joint_update_connection_806_tail 806 8128 32
 (Gval (Fuint 32) (rfa_reset_word_19 inputs path)) (Gval (Fuint 32) (rfa_reset_word_19 inputs path))
 (formal_invalid_policy inputs path) flat_memories old current result joint_update_connection_806_position joint_update_connection_806_split joint_update_connection_806_straight joint_update_connection_806_mid_safe joint_update_connection_806_tail_safe joint_update_connection_806_nonreg (Logic.eq_refl _) Source).
 - assert (Take : take 32 (rfa_reset_word_19 inputs path) = rfa_reset_word_19 inputs path).
   { apply take_oversize. rewrite rfa_reset_word_19_size. reflexivity. }
   cbn [adapt_hvalue_as_type]. rewrite Take. unfold zext_to,zext. rewrite rfa_reset_word_19_size subnn cats0. reflexivity.
 - exact Step.
Qed.
Theorem rfa_reset_history_806 inputs path history limit :
 (forall t, (t < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history t) false (history t) flat_statements = Some (history (S t))) ->
 forall t, (3 <= t)%coq_nat -> (t <= limit)%coq_nat ->
 VM.find 806 (history t) = Some (Gval (Fuint 32) (rfa_reset_word_19 inputs path)).
Proof.
 intros Steps t Lower Upper. destruct t as [|t]; [lia|].
 apply (rfa_reset_step_806 inputs path (history t) (history t) (history (S t))).
 - apply (rfa_reset_history_8128 inputs path history limit Steps t);lia.
 - apply Steps;lia.
Qed.
Definition rfa_node_1104_expr := joint_update_expr_1104.
Theorem rfa_reset_step_1104 inputs path old current result :
 VM.find 806 old = Some (Gval (Fuint 32) (rfa_reset_word_19 inputs path)) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 VM.find 1104 result = Some (Gval (Fuint 32) (rfa_reset_word_19 inputs path)).
Proof.
 intros Source Step.
 assert (Member : List.In (1104,joint_update_expr_1104) joint_update_expected_nodes).
 { apply (List.nth_error_In joint_update_expected_nodes 694%nat). vm_compute. reflexivity. }
 destruct (selected_node_safe_position flat_memories flat_statements joint_update_node_offsets flat_statements joint_update_expected_nodes 1104 joint_update_expr_1104 joint_update_node_positions joint_update_node_safety Member) as [count [tail [Position [Safe Nonreg]]]].
 eapply formal_combinational_known_node; [exact Position|exact Safe|exact Nonreg| |reflexivity|exact Step].
 cbn [rfa_node_1104_expr eval_hfexpr_validif_policy eval_href_validif_policy]. exact Source.
Qed.
Theorem rfa_reset_history_1104 inputs path history limit :
 (forall t, (t < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history t) false (history t) flat_statements = Some (history (S t))) ->
 forall t, (4 <= t)%coq_nat -> (t <= limit)%coq_nat ->
 VM.find 1104 (history t) = Some (Gval (Fuint 32) (rfa_reset_word_19 inputs path)).
Proof.
 intros Steps t Lower Upper. destruct t as [|t]; [lia|].
 apply (rfa_reset_step_1104 inputs path (history t) (history t) (history (S t))).
 - apply (rfa_reset_history_806 inputs path history limit Steps t);lia.
 - apply Steps;lia.
Qed.
Definition rfa_wire_1501_decl := match straight_drop 1581 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition rfa_wire_1501_tail := match straight_drop 8990 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition rfa_wire_1501_mid := take_statements 7408 rfa_wire_1501_decl.
Lemma rfa_wire_1501_position : straight_drop 1580 flat_statements = Some (@Qcons VarOrder.T (@Swire VarOrder.T 1501 (Gtyp (Fuint 32))) rfa_wire_1501_decl).
Proof. vm_compute. reflexivity. Qed.
Lemma rfa_wire_1501_split : rfa_wire_1501_decl = statement_append rfa_wire_1501_mid (@Qcons VarOrder.T (@Sfcnct VarOrder.T (@Eid VarOrder.T 1501) (@Eref VarOrder.T (@Eid VarOrder.T 8128))) rfa_wire_1501_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma rfa_wire_1501_straight : straight_statements rfa_wire_1501_mid.
Proof. vm_compute. exact I. Qed.
Lemma rfa_wire_1501_mid_safe : formal_typed_suffix_safe flat_memories 1501 rfa_wire_1501_mid.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma rfa_wire_1501_tail_safe : formal_typed_suffix_safe flat_memories 1501 rfa_wire_1501_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma rfa_wire_1501_nonreg : has_register 1501 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem rfa_reset_step_1501 inputs path old current result :
 VM.find 8128 old = Some (Gval (Fuint 32) (rfa_reset_word_19 inputs path)) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 VM.find 1501 result = Some (Gval (Fuint 32) (rfa_reset_word_19 inputs path)).
Proof.
 intros Source Step.
 apply (declared_connection_value 1580 flat_statements rfa_wire_1501_decl rfa_wire_1501_mid rfa_wire_1501_tail 1501 8128 32
 (Gval (Fuint 32) (rfa_reset_word_19 inputs path)) (Gval (Fuint 32) (rfa_reset_word_19 inputs path))
 (formal_invalid_policy inputs path) flat_memories old current result rfa_wire_1501_position rfa_wire_1501_split rfa_wire_1501_straight rfa_wire_1501_mid_safe rfa_wire_1501_tail_safe rfa_wire_1501_nonreg (Logic.eq_refl _) Source).
 - assert (Take : take 32 (rfa_reset_word_19 inputs path) = rfa_reset_word_19 inputs path).
   { apply take_oversize. rewrite rfa_reset_word_19_size. reflexivity. }
   cbn [adapt_hvalue_as_type]. rewrite Take. unfold zext_to,zext. rewrite rfa_reset_word_19_size subnn cats0. reflexivity.
 - exact Step.
Qed.
Theorem rfa_reset_history_1501 inputs path history limit :
 (forall t, (t < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history t) false (history t) flat_statements = Some (history (S t))) ->
 forall t, (3 <= t)%coq_nat -> (t <= limit)%coq_nat ->
 VM.find 1501 (history t) = Some (Gval (Fuint 32) (rfa_reset_word_19 inputs path)).
Proof.
 intros Steps t Lower Upper. destruct t as [|t]; [lia|].
 apply (rfa_reset_step_1501 inputs path (history t) (history t) (history (S t))).
 - apply (rfa_reset_history_8128 inputs path history limit Steps t);lia.
 - apply Steps;lia.
Qed.
Definition rfa_wire_1691_decl := match straight_drop 1771 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition rfa_wire_1691_tail := match straight_drop 8242 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition rfa_wire_1691_mid := take_statements 6470 rfa_wire_1691_decl.
Lemma rfa_wire_1691_position : straight_drop 1770 flat_statements = Some (@Qcons VarOrder.T (@Swire VarOrder.T 1691 (Gtyp (Fuint 32))) rfa_wire_1691_decl).
Proof. vm_compute. reflexivity. Qed.
Lemma rfa_wire_1691_split : rfa_wire_1691_decl = statement_append rfa_wire_1691_mid (@Qcons VarOrder.T (@Sfcnct VarOrder.T (@Eid VarOrder.T 1691) (@Eref VarOrder.T (@Eid VarOrder.T 1501))) rfa_wire_1691_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma rfa_wire_1691_straight : straight_statements rfa_wire_1691_mid.
Proof. vm_compute. exact I. Qed.
Lemma rfa_wire_1691_mid_safe : formal_typed_suffix_safe flat_memories 1691 rfa_wire_1691_mid.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma rfa_wire_1691_tail_safe : formal_typed_suffix_safe flat_memories 1691 rfa_wire_1691_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma rfa_wire_1691_nonreg : has_register 1691 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem rfa_reset_step_1691 inputs path old current result :
 VM.find 1501 old = Some (Gval (Fuint 32) (rfa_reset_word_19 inputs path)) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 VM.find 1691 result = Some (Gval (Fuint 32) (rfa_reset_word_19 inputs path)).
Proof.
 intros Source Step.
 apply (declared_connection_value 1770 flat_statements rfa_wire_1691_decl rfa_wire_1691_mid rfa_wire_1691_tail 1691 1501 32
 (Gval (Fuint 32) (rfa_reset_word_19 inputs path)) (Gval (Fuint 32) (rfa_reset_word_19 inputs path))
 (formal_invalid_policy inputs path) flat_memories old current result rfa_wire_1691_position rfa_wire_1691_split rfa_wire_1691_straight rfa_wire_1691_mid_safe rfa_wire_1691_tail_safe rfa_wire_1691_nonreg (Logic.eq_refl _) Source).
 - assert (Take : take 32 (rfa_reset_word_19 inputs path) = rfa_reset_word_19 inputs path).
   { apply take_oversize. rewrite rfa_reset_word_19_size. reflexivity. }
   cbn [adapt_hvalue_as_type]. rewrite Take. unfold zext_to,zext. rewrite rfa_reset_word_19_size subnn cats0. reflexivity.
 - exact Step.
Qed.
Theorem rfa_reset_history_1691 inputs path history limit :
 (forall t, (t < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history t) false (history t) flat_statements = Some (history (S t))) ->
 forall t, (4 <= t)%coq_nat -> (t <= limit)%coq_nat ->
 VM.find 1691 (history t) = Some (Gval (Fuint 32) (rfa_reset_word_19 inputs path)).
Proof.
 intros Steps t Lower Upper. destruct t as [|t]; [lia|].
 apply (rfa_reset_step_1691 inputs path (history t) (history t) (history (S t))).
 - apply (rfa_reset_history_1501 inputs path history limit Steps t);lia.
 - apply Steps;lia.
Qed.
Definition rfa_node_7407_expr := (@Eref VarOrder.T (@Eid VarOrder.T 1691)).
Definition rfa_node_7407_tail := match straight_drop 7579 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma rfa_node_7407_position : straight_drop 7578 flat_statements = Some (@Qcons VarOrder.T (@Snode VarOrder.T 7407 rfa_node_7407_expr) rfa_node_7407_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma rfa_node_7407_safe : formal_typed_suffix_safe flat_memories 7407 rfa_node_7407_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma rfa_node_7407_nonreg : has_register 7407 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem rfa_reset_step_7407 inputs path old current result :
 VM.find 1691 old = Some (Gval (Fuint 32) (rfa_reset_word_19 inputs path)) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 VM.find 7407 result = Some (Gval (Fuint 32) (rfa_reset_word_19 inputs path)).
Proof.
 intros Source Step.
 eapply formal_combinational_known_node;
 [exact rfa_node_7407_position|exact rfa_node_7407_safe|exact rfa_node_7407_nonreg| |reflexivity|exact Step].
 cbn [rfa_node_7407_expr eval_hfexpr_validif_policy eval_href_validif_policy]. exact Source.
Qed.
Theorem rfa_reset_history_7407 inputs path history limit :
 (forall t, (t < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history t) false (history t) flat_statements = Some (history (S t))) ->
 forall t, (5 <= t)%coq_nat -> (t <= limit)%coq_nat ->
 VM.find 7407 (history t) = Some (Gval (Fuint 32) (rfa_reset_word_19 inputs path)).
Proof.
 intros Steps t Lower Upper. destruct t as [|t]; [lia|].
 apply (rfa_reset_step_7407 inputs path (history t) (history t) (history (S t))).
 - apply (rfa_reset_history_1691 inputs path history limit Steps t);lia.
 - apply Steps;lia.
Qed.
Definition rfa_node_7408_expr := (@Eref VarOrder.T (@Eid VarOrder.T 7407)).
Definition rfa_node_7408_tail := match straight_drop 7580 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma rfa_node_7408_position : straight_drop 7579 flat_statements = Some (@Qcons VarOrder.T (@Snode VarOrder.T 7408 rfa_node_7408_expr) rfa_node_7408_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma rfa_node_7408_safe : formal_typed_suffix_safe flat_memories 7408 rfa_node_7408_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma rfa_node_7408_nonreg : has_register 7408 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem rfa_reset_step_7408 inputs path old current result :
 VM.find 7407 old = Some (Gval (Fuint 32) (rfa_reset_word_19 inputs path)) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 VM.find 7408 result = Some (Gval (Fuint 32) (rfa_reset_word_19 inputs path)).
Proof.
 intros Source Step.
 eapply formal_combinational_known_node;
 [exact rfa_node_7408_position|exact rfa_node_7408_safe|exact rfa_node_7408_nonreg| |reflexivity|exact Step].
 cbn [rfa_node_7408_expr eval_hfexpr_validif_policy eval_href_validif_policy]. exact Source.
Qed.
Theorem rfa_reset_history_7408 inputs path history limit :
 (forall t, (t < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history t) false (history t) flat_statements = Some (history (S t))) ->
 forall t, (6 <= t)%coq_nat -> (t <= limit)%coq_nat ->
 VM.find 7408 (history t) = Some (Gval (Fuint 32) (rfa_reset_word_19 inputs path)).
Proof.
 intros Steps t Lower Upper. destruct t as [|t]; [lia|].
 apply (rfa_reset_step_7408 inputs path (history t) (history t) (history (S t))).
 - apply (rfa_reset_history_7407 inputs path history limit Steps t);lia.
 - apply Steps;lia.
Qed.
