Require Import CoreSocModel ComparisonNodes ScalarNodeFrames FormalTypedNodeFrames RegisterInvariants FormalTypedNodeEquation FormalDeclaredConnection FormalStatementSegments RegisterCommitCertificate FormalUIntRegisterCommitSource SelectedUIntMuxIdentity UIntResizeRoundtrip.
From Coq Require Import ZArith List Lia.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From nbits Require Import NBits.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Definition rfa_reset_word_8 inputs path := proj1_sig (formal_symbolic_inputs inputs path (validif_source_address (validif_raw_address nil 8611 0 nil)) nil 32).
Lemma rfa_reset_word_8_size inputs path : size (rfa_reset_word_8 inputs path) = 32%nat.
Proof. exact (proj2_sig (formal_symbolic_inputs inputs path (validif_source_address (validif_raw_address nil 8611 0 nil)) nil 32)). Qed.
Definition rfa_node_8105_expr := (@Evalidif VarOrder.T (@Econst VarOrder.T (Fuint 1) [::false]) (@Econst VarOrder.T (Fuint 32) [::false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false])).
Definition rfa_node_8105_tail := match straight_drop 8612 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma rfa_node_8105_position : straight_drop 8611 flat_statements = Some (@Qcons VarOrder.T (@Snode VarOrder.T 8105 rfa_node_8105_expr) rfa_node_8105_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma rfa_node_8105_safe : formal_typed_suffix_safe flat_memories 8105 rfa_node_8105_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma rfa_node_8105_nonreg : has_register 8105 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem rfa_reset_step_8105 inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 VM.find 8105 result = Some (Gval (Fuint 32) (rfa_reset_word_8 inputs path)).
Proof.
 intros Step.
 eapply formal_combinational_known_node;
 [exact rfa_node_8105_position|exact rfa_node_8105_safe|exact rfa_node_8105_nonreg| |reflexivity|exact Step].
 reflexivity.
Qed.
Theorem rfa_reset_history_8105 inputs path history limit :
 (forall t, (t < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history t) false (history t) flat_statements = Some (history (S t))) ->
 forall t, (1 <= t)%coq_nat -> (t <= limit)%coq_nat ->
 VM.find 8105 (history t) = Some (Gval (Fuint 32) (rfa_reset_word_8 inputs path)).
Proof.
 intros Steps t Lower Upper. destruct t as [|t]; [lia|].
 apply (rfa_reset_step_8105 inputs path (history t) (history t) (history (S t))).
 apply Steps;lia.
Qed.
Definition rfa_node_8106_expr := (@Eref VarOrder.T (@Eid VarOrder.T 8105)).
Definition rfa_node_8106_tail := match straight_drop 8613 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma rfa_node_8106_position : straight_drop 8612 flat_statements = Some (@Qcons VarOrder.T (@Snode VarOrder.T 8106 rfa_node_8106_expr) rfa_node_8106_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma rfa_node_8106_safe : formal_typed_suffix_safe flat_memories 8106 rfa_node_8106_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma rfa_node_8106_nonreg : has_register 8106 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem rfa_reset_step_8106 inputs path old current result :
 VM.find 8105 old = Some (Gval (Fuint 32) (rfa_reset_word_8 inputs path)) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 VM.find 8106 result = Some (Gval (Fuint 32) (rfa_reset_word_8 inputs path)).
Proof.
 intros Source Step.
 eapply formal_combinational_known_node;
 [exact rfa_node_8106_position|exact rfa_node_8106_safe|exact rfa_node_8106_nonreg| |reflexivity|exact Step].
 cbn [rfa_node_8106_expr eval_hfexpr_validif_policy eval_href_validif_policy]. exact Source.
Qed.
Theorem rfa_reset_history_8106 inputs path history limit :
 (forall t, (t < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history t) false (history t) flat_statements = Some (history (S t))) ->
 forall t, (2 <= t)%coq_nat -> (t <= limit)%coq_nat ->
 VM.find 8106 (history t) = Some (Gval (Fuint 32) (rfa_reset_word_8 inputs path)).
Proof.
 intros Steps t Lower Upper. destruct t as [|t]; [lia|].
 apply (rfa_reset_step_8106 inputs path (history t) (history t) (history (S t))).
 - apply (rfa_reset_history_8105 inputs path history limit Steps t);lia.
 - apply Steps;lia.
Qed.
Definition rfa_wire_795_decl := match straight_drop 805 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition rfa_wire_795_tail := match straight_drop 8813 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition rfa_wire_795_mid := take_statements 8007 rfa_wire_795_decl.
Lemma rfa_wire_795_position : straight_drop 804 flat_statements = Some (@Qcons VarOrder.T (@Swire VarOrder.T 795 (Gtyp (Fuint 32))) rfa_wire_795_decl).
Proof. vm_compute. reflexivity. Qed.
Lemma rfa_wire_795_split : rfa_wire_795_decl = statement_append rfa_wire_795_mid (@Qcons VarOrder.T (@Sfcnct VarOrder.T (@Eid VarOrder.T 795) (@Eref VarOrder.T (@Eid VarOrder.T 8106))) rfa_wire_795_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma rfa_wire_795_straight : straight_statements rfa_wire_795_mid.
Proof. vm_compute. exact I. Qed.
Lemma rfa_wire_795_mid_safe : formal_typed_suffix_safe flat_memories 795 rfa_wire_795_mid.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma rfa_wire_795_tail_safe : formal_typed_suffix_safe flat_memories 795 rfa_wire_795_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma rfa_wire_795_nonreg : has_register 795 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem rfa_reset_step_795 inputs path old current result :
 VM.find 8106 old = Some (Gval (Fuint 32) (rfa_reset_word_8 inputs path)) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 VM.find 795 result = Some (Gval (Fuint 32) (rfa_reset_word_8 inputs path)).
Proof.
 intros Source Step.
 apply (declared_connection_value 804 flat_statements rfa_wire_795_decl rfa_wire_795_mid rfa_wire_795_tail 795 8106 32
 (Gval (Fuint 32) (rfa_reset_word_8 inputs path)) (Gval (Fuint 32) (rfa_reset_word_8 inputs path))
 (formal_invalid_policy inputs path) flat_memories old current result rfa_wire_795_position rfa_wire_795_split rfa_wire_795_straight rfa_wire_795_mid_safe rfa_wire_795_tail_safe rfa_wire_795_nonreg (Logic.eq_refl _) Source).
 - assert (Take : take 32 (rfa_reset_word_8 inputs path) = rfa_reset_word_8 inputs path).
   { apply take_oversize. rewrite rfa_reset_word_8_size. reflexivity. }
   cbn [adapt_hvalue_as_type]. rewrite Take. unfold zext_to,zext. rewrite rfa_reset_word_8_size subnn cats0. reflexivity.
 - exact Step.
Qed.
Theorem rfa_reset_history_795 inputs path history limit :
 (forall t, (t < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history t) false (history t) flat_statements = Some (history (S t))) ->
 forall t, (3 <= t)%coq_nat -> (t <= limit)%coq_nat ->
 VM.find 795 (history t) = Some (Gval (Fuint 32) (rfa_reset_word_8 inputs path)).
Proof.
 intros Steps t Lower Upper. destruct t as [|t]; [lia|].
 apply (rfa_reset_step_795 inputs path (history t) (history t) (history (S t))).
 - apply (rfa_reset_history_8106 inputs path history limit Steps t);lia.
 - apply Steps;lia.
Qed.
Definition rfa_node_1093_expr := (@Eref VarOrder.T (@Eid VarOrder.T 795)).
Definition rfa_node_1093_tail := match straight_drop 1103 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma rfa_node_1093_position : straight_drop 1102 flat_statements = Some (@Qcons VarOrder.T (@Snode VarOrder.T 1093 rfa_node_1093_expr) rfa_node_1093_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma rfa_node_1093_safe : formal_typed_suffix_safe flat_memories 1093 rfa_node_1093_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma rfa_node_1093_nonreg : has_register 1093 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem rfa_reset_step_1093 inputs path old current result :
 VM.find 795 old = Some (Gval (Fuint 32) (rfa_reset_word_8 inputs path)) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 VM.find 1093 result = Some (Gval (Fuint 32) (rfa_reset_word_8 inputs path)).
Proof.
 intros Source Step.
 eapply formal_combinational_known_node;
 [exact rfa_node_1093_position|exact rfa_node_1093_safe|exact rfa_node_1093_nonreg| |reflexivity|exact Step].
 cbn [rfa_node_1093_expr eval_hfexpr_validif_policy eval_href_validif_policy]. exact Source.
Qed.
Theorem rfa_reset_history_1093 inputs path history limit :
 (forall t, (t < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history t) false (history t) flat_statements = Some (history (S t))) ->
 forall t, (4 <= t)%coq_nat -> (t <= limit)%coq_nat ->
 VM.find 1093 (history t) = Some (Gval (Fuint 32) (rfa_reset_word_8 inputs path)).
Proof.
 intros Steps t Lower Upper. destruct t as [|t]; [lia|].
 apply (rfa_reset_step_1093 inputs path (history t) (history t) (history (S t))).
 - apply (rfa_reset_history_795 inputs path history limit Steps t);lia.
 - apply Steps;lia.
Qed.
Definition rfa_wire_1490_decl := match straight_drop 1570 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition rfa_wire_1490_tail := match straight_drop 8979 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition rfa_wire_1490_mid := take_statements 7408 rfa_wire_1490_decl.
Lemma rfa_wire_1490_position : straight_drop 1569 flat_statements = Some (@Qcons VarOrder.T (@Swire VarOrder.T 1490 (Gtyp (Fuint 32))) rfa_wire_1490_decl).
Proof. vm_compute. reflexivity. Qed.
Lemma rfa_wire_1490_split : rfa_wire_1490_decl = statement_append rfa_wire_1490_mid (@Qcons VarOrder.T (@Sfcnct VarOrder.T (@Eid VarOrder.T 1490) (@Eref VarOrder.T (@Eid VarOrder.T 8106))) rfa_wire_1490_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma rfa_wire_1490_straight : straight_statements rfa_wire_1490_mid.
Proof. vm_compute. exact I. Qed.
Lemma rfa_wire_1490_mid_safe : formal_typed_suffix_safe flat_memories 1490 rfa_wire_1490_mid.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma rfa_wire_1490_tail_safe : formal_typed_suffix_safe flat_memories 1490 rfa_wire_1490_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma rfa_wire_1490_nonreg : has_register 1490 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem rfa_reset_step_1490 inputs path old current result :
 VM.find 8106 old = Some (Gval (Fuint 32) (rfa_reset_word_8 inputs path)) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 VM.find 1490 result = Some (Gval (Fuint 32) (rfa_reset_word_8 inputs path)).
Proof.
 intros Source Step.
 apply (declared_connection_value 1569 flat_statements rfa_wire_1490_decl rfa_wire_1490_mid rfa_wire_1490_tail 1490 8106 32
 (Gval (Fuint 32) (rfa_reset_word_8 inputs path)) (Gval (Fuint 32) (rfa_reset_word_8 inputs path))
 (formal_invalid_policy inputs path) flat_memories old current result rfa_wire_1490_position rfa_wire_1490_split rfa_wire_1490_straight rfa_wire_1490_mid_safe rfa_wire_1490_tail_safe rfa_wire_1490_nonreg (Logic.eq_refl _) Source).
 - assert (Take : take 32 (rfa_reset_word_8 inputs path) = rfa_reset_word_8 inputs path).
   { apply take_oversize. rewrite rfa_reset_word_8_size. reflexivity. }
   cbn [adapt_hvalue_as_type]. rewrite Take. unfold zext_to,zext. rewrite rfa_reset_word_8_size subnn cats0. reflexivity.
 - exact Step.
Qed.
Theorem rfa_reset_history_1490 inputs path history limit :
 (forall t, (t < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history t) false (history t) flat_statements = Some (history (S t))) ->
 forall t, (3 <= t)%coq_nat -> (t <= limit)%coq_nat ->
 VM.find 1490 (history t) = Some (Gval (Fuint 32) (rfa_reset_word_8 inputs path)).
Proof.
 intros Steps t Lower Upper. destruct t as [|t]; [lia|].
 apply (rfa_reset_step_1490 inputs path (history t) (history t) (history (S t))).
 - apply (rfa_reset_history_8106 inputs path history limit Steps t);lia.
 - apply Steps;lia.
Qed.
Definition rfa_wire_1680_decl := match straight_drop 1760 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition rfa_wire_1680_tail := match straight_drop 8231 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition rfa_wire_1680_mid := take_statements 6470 rfa_wire_1680_decl.
Lemma rfa_wire_1680_position : straight_drop 1759 flat_statements = Some (@Qcons VarOrder.T (@Swire VarOrder.T 1680 (Gtyp (Fuint 32))) rfa_wire_1680_decl).
Proof. vm_compute. reflexivity. Qed.
Lemma rfa_wire_1680_split : rfa_wire_1680_decl = statement_append rfa_wire_1680_mid (@Qcons VarOrder.T (@Sfcnct VarOrder.T (@Eid VarOrder.T 1680) (@Eref VarOrder.T (@Eid VarOrder.T 1490))) rfa_wire_1680_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma rfa_wire_1680_straight : straight_statements rfa_wire_1680_mid.
Proof. vm_compute. exact I. Qed.
Lemma rfa_wire_1680_mid_safe : formal_typed_suffix_safe flat_memories 1680 rfa_wire_1680_mid.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma rfa_wire_1680_tail_safe : formal_typed_suffix_safe flat_memories 1680 rfa_wire_1680_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma rfa_wire_1680_nonreg : has_register 1680 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem rfa_reset_step_1680 inputs path old current result :
 VM.find 1490 old = Some (Gval (Fuint 32) (rfa_reset_word_8 inputs path)) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 VM.find 1680 result = Some (Gval (Fuint 32) (rfa_reset_word_8 inputs path)).
Proof.
 intros Source Step.
 apply (declared_connection_value 1759 flat_statements rfa_wire_1680_decl rfa_wire_1680_mid rfa_wire_1680_tail 1680 1490 32
 (Gval (Fuint 32) (rfa_reset_word_8 inputs path)) (Gval (Fuint 32) (rfa_reset_word_8 inputs path))
 (formal_invalid_policy inputs path) flat_memories old current result rfa_wire_1680_position rfa_wire_1680_split rfa_wire_1680_straight rfa_wire_1680_mid_safe rfa_wire_1680_tail_safe rfa_wire_1680_nonreg (Logic.eq_refl _) Source).
 - assert (Take : take 32 (rfa_reset_word_8 inputs path) = rfa_reset_word_8 inputs path).
   { apply take_oversize. rewrite rfa_reset_word_8_size. reflexivity. }
   cbn [adapt_hvalue_as_type]. rewrite Take. unfold zext_to,zext. rewrite rfa_reset_word_8_size subnn cats0. reflexivity.
 - exact Step.
Qed.
Theorem rfa_reset_history_1680 inputs path history limit :
 (forall t, (t < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history t) false (history t) flat_statements = Some (history (S t))) ->
 forall t, (4 <= t)%coq_nat -> (t <= limit)%coq_nat ->
 VM.find 1680 (history t) = Some (Gval (Fuint 32) (rfa_reset_word_8 inputs path)).
Proof.
 intros Steps t Lower Upper. destruct t as [|t]; [lia|].
 apply (rfa_reset_step_1680 inputs path (history t) (history t) (history (S t))).
 - apply (rfa_reset_history_1490 inputs path history limit Steps t);lia.
 - apply Steps;lia.
Qed.
Definition rfa_node_7385_expr := (@Eref VarOrder.T (@Eid VarOrder.T 1680)).
Definition rfa_node_7385_tail := match straight_drop 7557 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma rfa_node_7385_position : straight_drop 7556 flat_statements = Some (@Qcons VarOrder.T (@Snode VarOrder.T 7385 rfa_node_7385_expr) rfa_node_7385_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma rfa_node_7385_safe : formal_typed_suffix_safe flat_memories 7385 rfa_node_7385_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma rfa_node_7385_nonreg : has_register 7385 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem rfa_reset_step_7385 inputs path old current result :
 VM.find 1680 old = Some (Gval (Fuint 32) (rfa_reset_word_8 inputs path)) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 VM.find 7385 result = Some (Gval (Fuint 32) (rfa_reset_word_8 inputs path)).
Proof.
 intros Source Step.
 eapply formal_combinational_known_node;
 [exact rfa_node_7385_position|exact rfa_node_7385_safe|exact rfa_node_7385_nonreg| |reflexivity|exact Step].
 cbn [rfa_node_7385_expr eval_hfexpr_validif_policy eval_href_validif_policy]. exact Source.
Qed.
Theorem rfa_reset_history_7385 inputs path history limit :
 (forall t, (t < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history t) false (history t) flat_statements = Some (history (S t))) ->
 forall t, (5 <= t)%coq_nat -> (t <= limit)%coq_nat ->
 VM.find 7385 (history t) = Some (Gval (Fuint 32) (rfa_reset_word_8 inputs path)).
Proof.
 intros Steps t Lower Upper. destruct t as [|t]; [lia|].
 apply (rfa_reset_step_7385 inputs path (history t) (history t) (history (S t))).
 - apply (rfa_reset_history_1680 inputs path history limit Steps t);lia.
 - apply Steps;lia.
Qed.
Definition rfa_node_7386_expr := (@Eref VarOrder.T (@Eid VarOrder.T 7385)).
Definition rfa_node_7386_tail := match straight_drop 7558 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma rfa_node_7386_position : straight_drop 7557 flat_statements = Some (@Qcons VarOrder.T (@Snode VarOrder.T 7386 rfa_node_7386_expr) rfa_node_7386_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma rfa_node_7386_safe : formal_typed_suffix_safe flat_memories 7386 rfa_node_7386_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma rfa_node_7386_nonreg : has_register 7386 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem rfa_reset_step_7386 inputs path old current result :
 VM.find 7385 old = Some (Gval (Fuint 32) (rfa_reset_word_8 inputs path)) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 VM.find 7386 result = Some (Gval (Fuint 32) (rfa_reset_word_8 inputs path)).
Proof.
 intros Source Step.
 eapply formal_combinational_known_node;
 [exact rfa_node_7386_position|exact rfa_node_7386_safe|exact rfa_node_7386_nonreg| |reflexivity|exact Step].
 cbn [rfa_node_7386_expr eval_hfexpr_validif_policy eval_href_validif_policy]. exact Source.
Qed.
Theorem rfa_reset_history_7386 inputs path history limit :
 (forall t, (t < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history t) false (history t) flat_statements = Some (history (S t))) ->
 forall t, (6 <= t)%coq_nat -> (t <= limit)%coq_nat ->
 VM.find 7386 (history t) = Some (Gval (Fuint 32) (rfa_reset_word_8 inputs path)).
Proof.
 intros Steps t Lower Upper. destruct t as [|t]; [lia|].
 apply (rfa_reset_step_7386 inputs path (history t) (history t) (history (S t))).
 - apply (rfa_reset_history_7385 inputs path history limit Steps t);lia.
 - apply Steps;lia.
Qed.
Definition rfa_reset_word_9 inputs path := proj1_sig (formal_symbolic_inputs inputs path (validif_source_address (validif_raw_address nil 8613 0 nil)) nil 32).
Lemma rfa_reset_word_9_size inputs path : size (rfa_reset_word_9 inputs path) = 32%nat.
Proof. exact (proj2_sig (formal_symbolic_inputs inputs path (validif_source_address (validif_raw_address nil 8613 0 nil)) nil 32)). Qed.
Definition rfa_node_8107_expr := (@Evalidif VarOrder.T (@Econst VarOrder.T (Fuint 1) [::false]) (@Econst VarOrder.T (Fuint 32) [::false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false])).
Definition rfa_node_8107_tail := match straight_drop 8614 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma rfa_node_8107_position : straight_drop 8613 flat_statements = Some (@Qcons VarOrder.T (@Snode VarOrder.T 8107 rfa_node_8107_expr) rfa_node_8107_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma rfa_node_8107_safe : formal_typed_suffix_safe flat_memories 8107 rfa_node_8107_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma rfa_node_8107_nonreg : has_register 8107 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem rfa_reset_step_8107 inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 VM.find 8107 result = Some (Gval (Fuint 32) (rfa_reset_word_9 inputs path)).
Proof.
 intros Step.
 eapply formal_combinational_known_node;
 [exact rfa_node_8107_position|exact rfa_node_8107_safe|exact rfa_node_8107_nonreg| |reflexivity|exact Step].
 reflexivity.
Qed.
Theorem rfa_reset_history_8107 inputs path history limit :
 (forall t, (t < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history t) false (history t) flat_statements = Some (history (S t))) ->
 forall t, (1 <= t)%coq_nat -> (t <= limit)%coq_nat ->
 VM.find 8107 (history t) = Some (Gval (Fuint 32) (rfa_reset_word_9 inputs path)).
Proof.
 intros Steps t Lower Upper. destruct t as [|t]; [lia|].
 apply (rfa_reset_step_8107 inputs path (history t) (history t) (history (S t))).
 apply Steps;lia.
Qed.
Definition rfa_node_8108_expr := (@Eref VarOrder.T (@Eid VarOrder.T 8107)).
Definition rfa_node_8108_tail := match straight_drop 8615 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma rfa_node_8108_position : straight_drop 8614 flat_statements = Some (@Qcons VarOrder.T (@Snode VarOrder.T 8108 rfa_node_8108_expr) rfa_node_8108_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma rfa_node_8108_safe : formal_typed_suffix_safe flat_memories 8108 rfa_node_8108_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma rfa_node_8108_nonreg : has_register 8108 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem rfa_reset_step_8108 inputs path old current result :
 VM.find 8107 old = Some (Gval (Fuint 32) (rfa_reset_word_9 inputs path)) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 VM.find 8108 result = Some (Gval (Fuint 32) (rfa_reset_word_9 inputs path)).
Proof.
 intros Source Step.
 eapply formal_combinational_known_node;
 [exact rfa_node_8108_position|exact rfa_node_8108_safe|exact rfa_node_8108_nonreg| |reflexivity|exact Step].
 cbn [rfa_node_8108_expr eval_hfexpr_validif_policy eval_href_validif_policy]. exact Source.
Qed.
Theorem rfa_reset_history_8108 inputs path history limit :
 (forall t, (t < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history t) false (history t) flat_statements = Some (history (S t))) ->
 forall t, (2 <= t)%coq_nat -> (t <= limit)%coq_nat ->
 VM.find 8108 (history t) = Some (Gval (Fuint 32) (rfa_reset_word_9 inputs path)).
Proof.
 intros Steps t Lower Upper. destruct t as [|t]; [lia|].
 apply (rfa_reset_step_8108 inputs path (history t) (history t) (history (S t))).
 - apply (rfa_reset_history_8107 inputs path history limit Steps t);lia.
 - apply Steps;lia.
Qed.
Definition rfa_wire_796_decl := match straight_drop 806 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition rfa_wire_796_tail := match straight_drop 8814 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition rfa_wire_796_mid := take_statements 8007 rfa_wire_796_decl.
Lemma rfa_wire_796_position : straight_drop 805 flat_statements = Some (@Qcons VarOrder.T (@Swire VarOrder.T 796 (Gtyp (Fuint 32))) rfa_wire_796_decl).
Proof. vm_compute. reflexivity. Qed.
Lemma rfa_wire_796_split : rfa_wire_796_decl = statement_append rfa_wire_796_mid (@Qcons VarOrder.T (@Sfcnct VarOrder.T (@Eid VarOrder.T 796) (@Eref VarOrder.T (@Eid VarOrder.T 8108))) rfa_wire_796_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma rfa_wire_796_straight : straight_statements rfa_wire_796_mid.
Proof. vm_compute. exact I. Qed.
Lemma rfa_wire_796_mid_safe : formal_typed_suffix_safe flat_memories 796 rfa_wire_796_mid.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma rfa_wire_796_tail_safe : formal_typed_suffix_safe flat_memories 796 rfa_wire_796_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma rfa_wire_796_nonreg : has_register 796 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem rfa_reset_step_796 inputs path old current result :
 VM.find 8108 old = Some (Gval (Fuint 32) (rfa_reset_word_9 inputs path)) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 VM.find 796 result = Some (Gval (Fuint 32) (rfa_reset_word_9 inputs path)).
Proof.
 intros Source Step.
 apply (declared_connection_value 805 flat_statements rfa_wire_796_decl rfa_wire_796_mid rfa_wire_796_tail 796 8108 32
 (Gval (Fuint 32) (rfa_reset_word_9 inputs path)) (Gval (Fuint 32) (rfa_reset_word_9 inputs path))
 (formal_invalid_policy inputs path) flat_memories old current result rfa_wire_796_position rfa_wire_796_split rfa_wire_796_straight rfa_wire_796_mid_safe rfa_wire_796_tail_safe rfa_wire_796_nonreg (Logic.eq_refl _) Source).
 - assert (Take : take 32 (rfa_reset_word_9 inputs path) = rfa_reset_word_9 inputs path).
   { apply take_oversize. rewrite rfa_reset_word_9_size. reflexivity. }
   cbn [adapt_hvalue_as_type]. rewrite Take. unfold zext_to,zext. rewrite rfa_reset_word_9_size subnn cats0. reflexivity.
 - exact Step.
Qed.
Theorem rfa_reset_history_796 inputs path history limit :
 (forall t, (t < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history t) false (history t) flat_statements = Some (history (S t))) ->
 forall t, (3 <= t)%coq_nat -> (t <= limit)%coq_nat ->
 VM.find 796 (history t) = Some (Gval (Fuint 32) (rfa_reset_word_9 inputs path)).
Proof.
 intros Steps t Lower Upper. destruct t as [|t]; [lia|].
 apply (rfa_reset_step_796 inputs path (history t) (history t) (history (S t))).
 - apply (rfa_reset_history_8108 inputs path history limit Steps t);lia.
 - apply Steps;lia.
Qed.
Definition rfa_node_1094_expr := (@Eref VarOrder.T (@Eid VarOrder.T 796)).
Definition rfa_node_1094_tail := match straight_drop 1104 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma rfa_node_1094_position : straight_drop 1103 flat_statements = Some (@Qcons VarOrder.T (@Snode VarOrder.T 1094 rfa_node_1094_expr) rfa_node_1094_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma rfa_node_1094_safe : formal_typed_suffix_safe flat_memories 1094 rfa_node_1094_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma rfa_node_1094_nonreg : has_register 1094 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem rfa_reset_step_1094 inputs path old current result :
 VM.find 796 old = Some (Gval (Fuint 32) (rfa_reset_word_9 inputs path)) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 VM.find 1094 result = Some (Gval (Fuint 32) (rfa_reset_word_9 inputs path)).
Proof.
 intros Source Step.
 eapply formal_combinational_known_node;
 [exact rfa_node_1094_position|exact rfa_node_1094_safe|exact rfa_node_1094_nonreg| |reflexivity|exact Step].
 cbn [rfa_node_1094_expr eval_hfexpr_validif_policy eval_href_validif_policy]. exact Source.
Qed.
Theorem rfa_reset_history_1094 inputs path history limit :
 (forall t, (t < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history t) false (history t) flat_statements = Some (history (S t))) ->
 forall t, (4 <= t)%coq_nat -> (t <= limit)%coq_nat ->
 VM.find 1094 (history t) = Some (Gval (Fuint 32) (rfa_reset_word_9 inputs path)).
Proof.
 intros Steps t Lower Upper. destruct t as [|t]; [lia|].
 apply (rfa_reset_step_1094 inputs path (history t) (history t) (history (S t))).
 - apply (rfa_reset_history_796 inputs path history limit Steps t);lia.
 - apply Steps;lia.
Qed.
Definition rfa_wire_1491_decl := match straight_drop 1571 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition rfa_wire_1491_tail := match straight_drop 8980 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition rfa_wire_1491_mid := take_statements 7408 rfa_wire_1491_decl.
Lemma rfa_wire_1491_position : straight_drop 1570 flat_statements = Some (@Qcons VarOrder.T (@Swire VarOrder.T 1491 (Gtyp (Fuint 32))) rfa_wire_1491_decl).
Proof. vm_compute. reflexivity. Qed.
Lemma rfa_wire_1491_split : rfa_wire_1491_decl = statement_append rfa_wire_1491_mid (@Qcons VarOrder.T (@Sfcnct VarOrder.T (@Eid VarOrder.T 1491) (@Eref VarOrder.T (@Eid VarOrder.T 8108))) rfa_wire_1491_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma rfa_wire_1491_straight : straight_statements rfa_wire_1491_mid.
Proof. vm_compute. exact I. Qed.
Lemma rfa_wire_1491_mid_safe : formal_typed_suffix_safe flat_memories 1491 rfa_wire_1491_mid.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma rfa_wire_1491_tail_safe : formal_typed_suffix_safe flat_memories 1491 rfa_wire_1491_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma rfa_wire_1491_nonreg : has_register 1491 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem rfa_reset_step_1491 inputs path old current result :
 VM.find 8108 old = Some (Gval (Fuint 32) (rfa_reset_word_9 inputs path)) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 VM.find 1491 result = Some (Gval (Fuint 32) (rfa_reset_word_9 inputs path)).
Proof.
 intros Source Step.
 apply (declared_connection_value 1570 flat_statements rfa_wire_1491_decl rfa_wire_1491_mid rfa_wire_1491_tail 1491 8108 32
 (Gval (Fuint 32) (rfa_reset_word_9 inputs path)) (Gval (Fuint 32) (rfa_reset_word_9 inputs path))
 (formal_invalid_policy inputs path) flat_memories old current result rfa_wire_1491_position rfa_wire_1491_split rfa_wire_1491_straight rfa_wire_1491_mid_safe rfa_wire_1491_tail_safe rfa_wire_1491_nonreg (Logic.eq_refl _) Source).
 - assert (Take : take 32 (rfa_reset_word_9 inputs path) = rfa_reset_word_9 inputs path).
   { apply take_oversize. rewrite rfa_reset_word_9_size. reflexivity. }
   cbn [adapt_hvalue_as_type]. rewrite Take. unfold zext_to,zext. rewrite rfa_reset_word_9_size subnn cats0. reflexivity.
 - exact Step.
Qed.
Theorem rfa_reset_history_1491 inputs path history limit :
 (forall t, (t < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history t) false (history t) flat_statements = Some (history (S t))) ->
 forall t, (3 <= t)%coq_nat -> (t <= limit)%coq_nat ->
 VM.find 1491 (history t) = Some (Gval (Fuint 32) (rfa_reset_word_9 inputs path)).
Proof.
 intros Steps t Lower Upper. destruct t as [|t]; [lia|].
 apply (rfa_reset_step_1491 inputs path (history t) (history t) (history (S t))).
 - apply (rfa_reset_history_8108 inputs path history limit Steps t);lia.
 - apply Steps;lia.
Qed.
Definition rfa_wire_1681_decl := match straight_drop 1761 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition rfa_wire_1681_tail := match straight_drop 8232 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition rfa_wire_1681_mid := take_statements 6470 rfa_wire_1681_decl.
Lemma rfa_wire_1681_position : straight_drop 1760 flat_statements = Some (@Qcons VarOrder.T (@Swire VarOrder.T 1681 (Gtyp (Fuint 32))) rfa_wire_1681_decl).
Proof. vm_compute. reflexivity. Qed.
Lemma rfa_wire_1681_split : rfa_wire_1681_decl = statement_append rfa_wire_1681_mid (@Qcons VarOrder.T (@Sfcnct VarOrder.T (@Eid VarOrder.T 1681) (@Eref VarOrder.T (@Eid VarOrder.T 1491))) rfa_wire_1681_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma rfa_wire_1681_straight : straight_statements rfa_wire_1681_mid.
Proof. vm_compute. exact I. Qed.
Lemma rfa_wire_1681_mid_safe : formal_typed_suffix_safe flat_memories 1681 rfa_wire_1681_mid.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma rfa_wire_1681_tail_safe : formal_typed_suffix_safe flat_memories 1681 rfa_wire_1681_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma rfa_wire_1681_nonreg : has_register 1681 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem rfa_reset_step_1681 inputs path old current result :
 VM.find 1491 old = Some (Gval (Fuint 32) (rfa_reset_word_9 inputs path)) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 VM.find 1681 result = Some (Gval (Fuint 32) (rfa_reset_word_9 inputs path)).
Proof.
 intros Source Step.
 apply (declared_connection_value 1760 flat_statements rfa_wire_1681_decl rfa_wire_1681_mid rfa_wire_1681_tail 1681 1491 32
 (Gval (Fuint 32) (rfa_reset_word_9 inputs path)) (Gval (Fuint 32) (rfa_reset_word_9 inputs path))
 (formal_invalid_policy inputs path) flat_memories old current result rfa_wire_1681_position rfa_wire_1681_split rfa_wire_1681_straight rfa_wire_1681_mid_safe rfa_wire_1681_tail_safe rfa_wire_1681_nonreg (Logic.eq_refl _) Source).
 - assert (Take : take 32 (rfa_reset_word_9 inputs path) = rfa_reset_word_9 inputs path).
   { apply take_oversize. rewrite rfa_reset_word_9_size. reflexivity. }
   cbn [adapt_hvalue_as_type]. rewrite Take. unfold zext_to,zext. rewrite rfa_reset_word_9_size subnn cats0. reflexivity.
 - exact Step.
Qed.
Theorem rfa_reset_history_1681 inputs path history limit :
 (forall t, (t < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history t) false (history t) flat_statements = Some (history (S t))) ->
 forall t, (4 <= t)%coq_nat -> (t <= limit)%coq_nat ->
 VM.find 1681 (history t) = Some (Gval (Fuint 32) (rfa_reset_word_9 inputs path)).
Proof.
 intros Steps t Lower Upper. destruct t as [|t]; [lia|].
 apply (rfa_reset_step_1681 inputs path (history t) (history t) (history (S t))).
 - apply (rfa_reset_history_1491 inputs path history limit Steps t);lia.
 - apply Steps;lia.
Qed.
Definition rfa_node_7387_expr := (@Eref VarOrder.T (@Eid VarOrder.T 1681)).
Definition rfa_node_7387_tail := match straight_drop 7559 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma rfa_node_7387_position : straight_drop 7558 flat_statements = Some (@Qcons VarOrder.T (@Snode VarOrder.T 7387 rfa_node_7387_expr) rfa_node_7387_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma rfa_node_7387_safe : formal_typed_suffix_safe flat_memories 7387 rfa_node_7387_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma rfa_node_7387_nonreg : has_register 7387 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem rfa_reset_step_7387 inputs path old current result :
 VM.find 1681 old = Some (Gval (Fuint 32) (rfa_reset_word_9 inputs path)) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 VM.find 7387 result = Some (Gval (Fuint 32) (rfa_reset_word_9 inputs path)).
Proof.
 intros Source Step.
 eapply formal_combinational_known_node;
 [exact rfa_node_7387_position|exact rfa_node_7387_safe|exact rfa_node_7387_nonreg| |reflexivity|exact Step].
 cbn [rfa_node_7387_expr eval_hfexpr_validif_policy eval_href_validif_policy]. exact Source.
Qed.
Theorem rfa_reset_history_7387 inputs path history limit :
 (forall t, (t < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history t) false (history t) flat_statements = Some (history (S t))) ->
 forall t, (5 <= t)%coq_nat -> (t <= limit)%coq_nat ->
 VM.find 7387 (history t) = Some (Gval (Fuint 32) (rfa_reset_word_9 inputs path)).
Proof.
 intros Steps t Lower Upper. destruct t as [|t]; [lia|].
 apply (rfa_reset_step_7387 inputs path (history t) (history t) (history (S t))).
 - apply (rfa_reset_history_1681 inputs path history limit Steps t);lia.
 - apply Steps;lia.
Qed.
Definition rfa_node_7388_expr := (@Eref VarOrder.T (@Eid VarOrder.T 7387)).
Definition rfa_node_7388_tail := match straight_drop 7560 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma rfa_node_7388_position : straight_drop 7559 flat_statements = Some (@Qcons VarOrder.T (@Snode VarOrder.T 7388 rfa_node_7388_expr) rfa_node_7388_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma rfa_node_7388_safe : formal_typed_suffix_safe flat_memories 7388 rfa_node_7388_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma rfa_node_7388_nonreg : has_register 7388 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem rfa_reset_step_7388 inputs path old current result :
 VM.find 7387 old = Some (Gval (Fuint 32) (rfa_reset_word_9 inputs path)) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 VM.find 7388 result = Some (Gval (Fuint 32) (rfa_reset_word_9 inputs path)).
Proof.
 intros Source Step.
 eapply formal_combinational_known_node;
 [exact rfa_node_7388_position|exact rfa_node_7388_safe|exact rfa_node_7388_nonreg| |reflexivity|exact Step].
 cbn [rfa_node_7388_expr eval_hfexpr_validif_policy eval_href_validif_policy]. exact Source.
Qed.
Theorem rfa_reset_history_7388 inputs path history limit :
 (forall t, (t < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history t) false (history t) flat_statements = Some (history (S t))) ->
 forall t, (6 <= t)%coq_nat -> (t <= limit)%coq_nat ->
 VM.find 7388 (history t) = Some (Gval (Fuint 32) (rfa_reset_word_9 inputs path)).
Proof.
 intros Steps t Lower Upper. destruct t as [|t]; [lia|].
 apply (rfa_reset_step_7388 inputs path (history t) (history t) (history (S t))).
 - apply (rfa_reset_history_7387 inputs path history limit Steps t);lia.
 - apply Steps;lia.
Qed.
Definition rfa_reset_word_10 inputs path := proj1_sig (formal_symbolic_inputs inputs path (validif_source_address (validif_raw_address nil 8615 0 nil)) nil 32).
Lemma rfa_reset_word_10_size inputs path : size (rfa_reset_word_10 inputs path) = 32%nat.
Proof. exact (proj2_sig (formal_symbolic_inputs inputs path (validif_source_address (validif_raw_address nil 8615 0 nil)) nil 32)). Qed.
Definition rfa_node_8109_expr := (@Evalidif VarOrder.T (@Econst VarOrder.T (Fuint 1) [::false]) (@Econst VarOrder.T (Fuint 32) [::false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false])).
Definition rfa_node_8109_tail := match straight_drop 8616 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma rfa_node_8109_position : straight_drop 8615 flat_statements = Some (@Qcons VarOrder.T (@Snode VarOrder.T 8109 rfa_node_8109_expr) rfa_node_8109_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma rfa_node_8109_safe : formal_typed_suffix_safe flat_memories 8109 rfa_node_8109_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma rfa_node_8109_nonreg : has_register 8109 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem rfa_reset_step_8109 inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 VM.find 8109 result = Some (Gval (Fuint 32) (rfa_reset_word_10 inputs path)).
Proof.
 intros Step.
 eapply formal_combinational_known_node;
 [exact rfa_node_8109_position|exact rfa_node_8109_safe|exact rfa_node_8109_nonreg| |reflexivity|exact Step].
 reflexivity.
Qed.
Theorem rfa_reset_history_8109 inputs path history limit :
 (forall t, (t < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history t) false (history t) flat_statements = Some (history (S t))) ->
 forall t, (1 <= t)%coq_nat -> (t <= limit)%coq_nat ->
 VM.find 8109 (history t) = Some (Gval (Fuint 32) (rfa_reset_word_10 inputs path)).
Proof.
 intros Steps t Lower Upper. destruct t as [|t]; [lia|].
 apply (rfa_reset_step_8109 inputs path (history t) (history t) (history (S t))).
 apply Steps;lia.
Qed.
Definition rfa_node_8110_expr := (@Eref VarOrder.T (@Eid VarOrder.T 8109)).
Definition rfa_node_8110_tail := match straight_drop 8617 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma rfa_node_8110_position : straight_drop 8616 flat_statements = Some (@Qcons VarOrder.T (@Snode VarOrder.T 8110 rfa_node_8110_expr) rfa_node_8110_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma rfa_node_8110_safe : formal_typed_suffix_safe flat_memories 8110 rfa_node_8110_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma rfa_node_8110_nonreg : has_register 8110 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem rfa_reset_step_8110 inputs path old current result :
 VM.find 8109 old = Some (Gval (Fuint 32) (rfa_reset_word_10 inputs path)) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 VM.find 8110 result = Some (Gval (Fuint 32) (rfa_reset_word_10 inputs path)).
Proof.
 intros Source Step.
 eapply formal_combinational_known_node;
 [exact rfa_node_8110_position|exact rfa_node_8110_safe|exact rfa_node_8110_nonreg| |reflexivity|exact Step].
 cbn [rfa_node_8110_expr eval_hfexpr_validif_policy eval_href_validif_policy]. exact Source.
Qed.
Theorem rfa_reset_history_8110 inputs path history limit :
 (forall t, (t < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history t) false (history t) flat_statements = Some (history (S t))) ->
 forall t, (2 <= t)%coq_nat -> (t <= limit)%coq_nat ->
 VM.find 8110 (history t) = Some (Gval (Fuint 32) (rfa_reset_word_10 inputs path)).
Proof.
 intros Steps t Lower Upper. destruct t as [|t]; [lia|].
 apply (rfa_reset_step_8110 inputs path (history t) (history t) (history (S t))).
 - apply (rfa_reset_history_8109 inputs path history limit Steps t);lia.
 - apply Steps;lia.
Qed.
Definition rfa_wire_797_decl := match straight_drop 807 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition rfa_wire_797_tail := match straight_drop 8815 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition rfa_wire_797_mid := take_statements 8007 rfa_wire_797_decl.
Lemma rfa_wire_797_position : straight_drop 806 flat_statements = Some (@Qcons VarOrder.T (@Swire VarOrder.T 797 (Gtyp (Fuint 32))) rfa_wire_797_decl).
Proof. vm_compute. reflexivity. Qed.
Lemma rfa_wire_797_split : rfa_wire_797_decl = statement_append rfa_wire_797_mid (@Qcons VarOrder.T (@Sfcnct VarOrder.T (@Eid VarOrder.T 797) (@Eref VarOrder.T (@Eid VarOrder.T 8110))) rfa_wire_797_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma rfa_wire_797_straight : straight_statements rfa_wire_797_mid.
Proof. vm_compute. exact I. Qed.
Lemma rfa_wire_797_mid_safe : formal_typed_suffix_safe flat_memories 797 rfa_wire_797_mid.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma rfa_wire_797_tail_safe : formal_typed_suffix_safe flat_memories 797 rfa_wire_797_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma rfa_wire_797_nonreg : has_register 797 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem rfa_reset_step_797 inputs path old current result :
 VM.find 8110 old = Some (Gval (Fuint 32) (rfa_reset_word_10 inputs path)) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 VM.find 797 result = Some (Gval (Fuint 32) (rfa_reset_word_10 inputs path)).
Proof.
 intros Source Step.
 apply (declared_connection_value 806 flat_statements rfa_wire_797_decl rfa_wire_797_mid rfa_wire_797_tail 797 8110 32
 (Gval (Fuint 32) (rfa_reset_word_10 inputs path)) (Gval (Fuint 32) (rfa_reset_word_10 inputs path))
 (formal_invalid_policy inputs path) flat_memories old current result rfa_wire_797_position rfa_wire_797_split rfa_wire_797_straight rfa_wire_797_mid_safe rfa_wire_797_tail_safe rfa_wire_797_nonreg (Logic.eq_refl _) Source).
 - assert (Take : take 32 (rfa_reset_word_10 inputs path) = rfa_reset_word_10 inputs path).
   { apply take_oversize. rewrite rfa_reset_word_10_size. reflexivity. }
   cbn [adapt_hvalue_as_type]. rewrite Take. unfold zext_to,zext. rewrite rfa_reset_word_10_size subnn cats0. reflexivity.
 - exact Step.
Qed.
Theorem rfa_reset_history_797 inputs path history limit :
 (forall t, (t < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history t) false (history t) flat_statements = Some (history (S t))) ->
 forall t, (3 <= t)%coq_nat -> (t <= limit)%coq_nat ->
 VM.find 797 (history t) = Some (Gval (Fuint 32) (rfa_reset_word_10 inputs path)).
Proof.
 intros Steps t Lower Upper. destruct t as [|t]; [lia|].
 apply (rfa_reset_step_797 inputs path (history t) (history t) (history (S t))).
 - apply (rfa_reset_history_8110 inputs path history limit Steps t);lia.
 - apply Steps;lia.
Qed.
Definition rfa_node_1095_expr := (@Eref VarOrder.T (@Eid VarOrder.T 797)).
Definition rfa_node_1095_tail := match straight_drop 1105 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma rfa_node_1095_position : straight_drop 1104 flat_statements = Some (@Qcons VarOrder.T (@Snode VarOrder.T 1095 rfa_node_1095_expr) rfa_node_1095_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma rfa_node_1095_safe : formal_typed_suffix_safe flat_memories 1095 rfa_node_1095_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma rfa_node_1095_nonreg : has_register 1095 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem rfa_reset_step_1095 inputs path old current result :
 VM.find 797 old = Some (Gval (Fuint 32) (rfa_reset_word_10 inputs path)) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 VM.find 1095 result = Some (Gval (Fuint 32) (rfa_reset_word_10 inputs path)).
Proof.
 intros Source Step.
 eapply formal_combinational_known_node;
 [exact rfa_node_1095_position|exact rfa_node_1095_safe|exact rfa_node_1095_nonreg| |reflexivity|exact Step].
 cbn [rfa_node_1095_expr eval_hfexpr_validif_policy eval_href_validif_policy]. exact Source.
Qed.
Theorem rfa_reset_history_1095 inputs path history limit :
 (forall t, (t < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history t) false (history t) flat_statements = Some (history (S t))) ->
 forall t, (4 <= t)%coq_nat -> (t <= limit)%coq_nat ->
 VM.find 1095 (history t) = Some (Gval (Fuint 32) (rfa_reset_word_10 inputs path)).
Proof.
 intros Steps t Lower Upper. destruct t as [|t]; [lia|].
 apply (rfa_reset_step_1095 inputs path (history t) (history t) (history (S t))).
 - apply (rfa_reset_history_797 inputs path history limit Steps t);lia.
 - apply Steps;lia.
Qed.
Definition rfa_wire_1492_decl := match straight_drop 1572 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition rfa_wire_1492_tail := match straight_drop 8981 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition rfa_wire_1492_mid := take_statements 7408 rfa_wire_1492_decl.
Lemma rfa_wire_1492_position : straight_drop 1571 flat_statements = Some (@Qcons VarOrder.T (@Swire VarOrder.T 1492 (Gtyp (Fuint 32))) rfa_wire_1492_decl).
Proof. vm_compute. reflexivity. Qed.
Lemma rfa_wire_1492_split : rfa_wire_1492_decl = statement_append rfa_wire_1492_mid (@Qcons VarOrder.T (@Sfcnct VarOrder.T (@Eid VarOrder.T 1492) (@Eref VarOrder.T (@Eid VarOrder.T 8110))) rfa_wire_1492_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma rfa_wire_1492_straight : straight_statements rfa_wire_1492_mid.
Proof. vm_compute. exact I. Qed.
Lemma rfa_wire_1492_mid_safe : formal_typed_suffix_safe flat_memories 1492 rfa_wire_1492_mid.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma rfa_wire_1492_tail_safe : formal_typed_suffix_safe flat_memories 1492 rfa_wire_1492_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma rfa_wire_1492_nonreg : has_register 1492 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem rfa_reset_step_1492 inputs path old current result :
 VM.find 8110 old = Some (Gval (Fuint 32) (rfa_reset_word_10 inputs path)) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 VM.find 1492 result = Some (Gval (Fuint 32) (rfa_reset_word_10 inputs path)).
Proof.
 intros Source Step.
 apply (declared_connection_value 1571 flat_statements rfa_wire_1492_decl rfa_wire_1492_mid rfa_wire_1492_tail 1492 8110 32
 (Gval (Fuint 32) (rfa_reset_word_10 inputs path)) (Gval (Fuint 32) (rfa_reset_word_10 inputs path))
 (formal_invalid_policy inputs path) flat_memories old current result rfa_wire_1492_position rfa_wire_1492_split rfa_wire_1492_straight rfa_wire_1492_mid_safe rfa_wire_1492_tail_safe rfa_wire_1492_nonreg (Logic.eq_refl _) Source).
 - assert (Take : take 32 (rfa_reset_word_10 inputs path) = rfa_reset_word_10 inputs path).
   { apply take_oversize. rewrite rfa_reset_word_10_size. reflexivity. }
   cbn [adapt_hvalue_as_type]. rewrite Take. unfold zext_to,zext. rewrite rfa_reset_word_10_size subnn cats0. reflexivity.
 - exact Step.
Qed.
Theorem rfa_reset_history_1492 inputs path history limit :
 (forall t, (t < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history t) false (history t) flat_statements = Some (history (S t))) ->
 forall t, (3 <= t)%coq_nat -> (t <= limit)%coq_nat ->
 VM.find 1492 (history t) = Some (Gval (Fuint 32) (rfa_reset_word_10 inputs path)).
Proof.
 intros Steps t Lower Upper. destruct t as [|t]; [lia|].
 apply (rfa_reset_step_1492 inputs path (history t) (history t) (history (S t))).
 - apply (rfa_reset_history_8110 inputs path history limit Steps t);lia.
 - apply Steps;lia.
Qed.
Definition rfa_wire_1682_decl := match straight_drop 1762 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition rfa_wire_1682_tail := match straight_drop 8233 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition rfa_wire_1682_mid := take_statements 6470 rfa_wire_1682_decl.
Lemma rfa_wire_1682_position : straight_drop 1761 flat_statements = Some (@Qcons VarOrder.T (@Swire VarOrder.T 1682 (Gtyp (Fuint 32))) rfa_wire_1682_decl).
Proof. vm_compute. reflexivity. Qed.
Lemma rfa_wire_1682_split : rfa_wire_1682_decl = statement_append rfa_wire_1682_mid (@Qcons VarOrder.T (@Sfcnct VarOrder.T (@Eid VarOrder.T 1682) (@Eref VarOrder.T (@Eid VarOrder.T 1492))) rfa_wire_1682_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma rfa_wire_1682_straight : straight_statements rfa_wire_1682_mid.
Proof. vm_compute. exact I. Qed.
Lemma rfa_wire_1682_mid_safe : formal_typed_suffix_safe flat_memories 1682 rfa_wire_1682_mid.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma rfa_wire_1682_tail_safe : formal_typed_suffix_safe flat_memories 1682 rfa_wire_1682_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma rfa_wire_1682_nonreg : has_register 1682 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem rfa_reset_step_1682 inputs path old current result :
 VM.find 1492 old = Some (Gval (Fuint 32) (rfa_reset_word_10 inputs path)) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 VM.find 1682 result = Some (Gval (Fuint 32) (rfa_reset_word_10 inputs path)).
Proof.
 intros Source Step.
 apply (declared_connection_value 1761 flat_statements rfa_wire_1682_decl rfa_wire_1682_mid rfa_wire_1682_tail 1682 1492 32
 (Gval (Fuint 32) (rfa_reset_word_10 inputs path)) (Gval (Fuint 32) (rfa_reset_word_10 inputs path))
 (formal_invalid_policy inputs path) flat_memories old current result rfa_wire_1682_position rfa_wire_1682_split rfa_wire_1682_straight rfa_wire_1682_mid_safe rfa_wire_1682_tail_safe rfa_wire_1682_nonreg (Logic.eq_refl _) Source).
 - assert (Take : take 32 (rfa_reset_word_10 inputs path) = rfa_reset_word_10 inputs path).
   { apply take_oversize. rewrite rfa_reset_word_10_size. reflexivity. }
   cbn [adapt_hvalue_as_type]. rewrite Take. unfold zext_to,zext. rewrite rfa_reset_word_10_size subnn cats0. reflexivity.
 - exact Step.
Qed.
Theorem rfa_reset_history_1682 inputs path history limit :
 (forall t, (t < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history t) false (history t) flat_statements = Some (history (S t))) ->
 forall t, (4 <= t)%coq_nat -> (t <= limit)%coq_nat ->
 VM.find 1682 (history t) = Some (Gval (Fuint 32) (rfa_reset_word_10 inputs path)).
Proof.
 intros Steps t Lower Upper. destruct t as [|t]; [lia|].
 apply (rfa_reset_step_1682 inputs path (history t) (history t) (history (S t))).
 - apply (rfa_reset_history_1492 inputs path history limit Steps t);lia.
 - apply Steps;lia.
Qed.
Definition rfa_node_7389_expr := (@Eref VarOrder.T (@Eid VarOrder.T 1682)).
Definition rfa_node_7389_tail := match straight_drop 7561 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma rfa_node_7389_position : straight_drop 7560 flat_statements = Some (@Qcons VarOrder.T (@Snode VarOrder.T 7389 rfa_node_7389_expr) rfa_node_7389_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma rfa_node_7389_safe : formal_typed_suffix_safe flat_memories 7389 rfa_node_7389_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma rfa_node_7389_nonreg : has_register 7389 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem rfa_reset_step_7389 inputs path old current result :
 VM.find 1682 old = Some (Gval (Fuint 32) (rfa_reset_word_10 inputs path)) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 VM.find 7389 result = Some (Gval (Fuint 32) (rfa_reset_word_10 inputs path)).
Proof.
 intros Source Step.
 eapply formal_combinational_known_node;
 [exact rfa_node_7389_position|exact rfa_node_7389_safe|exact rfa_node_7389_nonreg| |reflexivity|exact Step].
 cbn [rfa_node_7389_expr eval_hfexpr_validif_policy eval_href_validif_policy]. exact Source.
Qed.
Theorem rfa_reset_history_7389 inputs path history limit :
 (forall t, (t < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history t) false (history t) flat_statements = Some (history (S t))) ->
 forall t, (5 <= t)%coq_nat -> (t <= limit)%coq_nat ->
 VM.find 7389 (history t) = Some (Gval (Fuint 32) (rfa_reset_word_10 inputs path)).
Proof.
 intros Steps t Lower Upper. destruct t as [|t]; [lia|].
 apply (rfa_reset_step_7389 inputs path (history t) (history t) (history (S t))).
 - apply (rfa_reset_history_1682 inputs path history limit Steps t);lia.
 - apply Steps;lia.
Qed.
Definition rfa_node_7390_expr := (@Eref VarOrder.T (@Eid VarOrder.T 7389)).
Definition rfa_node_7390_tail := match straight_drop 7562 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma rfa_node_7390_position : straight_drop 7561 flat_statements = Some (@Qcons VarOrder.T (@Snode VarOrder.T 7390 rfa_node_7390_expr) rfa_node_7390_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma rfa_node_7390_safe : formal_typed_suffix_safe flat_memories 7390 rfa_node_7390_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma rfa_node_7390_nonreg : has_register 7390 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem rfa_reset_step_7390 inputs path old current result :
 VM.find 7389 old = Some (Gval (Fuint 32) (rfa_reset_word_10 inputs path)) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 VM.find 7390 result = Some (Gval (Fuint 32) (rfa_reset_word_10 inputs path)).
Proof.
 intros Source Step.
 eapply formal_combinational_known_node;
 [exact rfa_node_7390_position|exact rfa_node_7390_safe|exact rfa_node_7390_nonreg| |reflexivity|exact Step].
 cbn [rfa_node_7390_expr eval_hfexpr_validif_policy eval_href_validif_policy]. exact Source.
Qed.
Theorem rfa_reset_history_7390 inputs path history limit :
 (forall t, (t < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history t) false (history t) flat_statements = Some (history (S t))) ->
 forall t, (6 <= t)%coq_nat -> (t <= limit)%coq_nat ->
 VM.find 7390 (history t) = Some (Gval (Fuint 32) (rfa_reset_word_10 inputs path)).
Proof.
 intros Steps t Lower Upper. destruct t as [|t]; [lia|].
 apply (rfa_reset_step_7390 inputs path (history t) (history t) (history (S t))).
 - apply (rfa_reset_history_7389 inputs path history limit Steps t);lia.
 - apply Steps;lia.
Qed.
Definition rfa_reset_word_11 inputs path := proj1_sig (formal_symbolic_inputs inputs path (validif_source_address (validif_raw_address nil 8617 0 nil)) nil 32).
Lemma rfa_reset_word_11_size inputs path : size (rfa_reset_word_11 inputs path) = 32%nat.
Proof. exact (proj2_sig (formal_symbolic_inputs inputs path (validif_source_address (validif_raw_address nil 8617 0 nil)) nil 32)). Qed.
Definition rfa_node_8111_expr := (@Evalidif VarOrder.T (@Econst VarOrder.T (Fuint 1) [::false]) (@Econst VarOrder.T (Fuint 32) [::false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false])).
Definition rfa_node_8111_tail := match straight_drop 8618 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma rfa_node_8111_position : straight_drop 8617 flat_statements = Some (@Qcons VarOrder.T (@Snode VarOrder.T 8111 rfa_node_8111_expr) rfa_node_8111_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma rfa_node_8111_safe : formal_typed_suffix_safe flat_memories 8111 rfa_node_8111_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma rfa_node_8111_nonreg : has_register 8111 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem rfa_reset_step_8111 inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 VM.find 8111 result = Some (Gval (Fuint 32) (rfa_reset_word_11 inputs path)).
Proof.
 intros Step.
 eapply formal_combinational_known_node;
 [exact rfa_node_8111_position|exact rfa_node_8111_safe|exact rfa_node_8111_nonreg| |reflexivity|exact Step].
 reflexivity.
Qed.
Theorem rfa_reset_history_8111 inputs path history limit :
 (forall t, (t < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history t) false (history t) flat_statements = Some (history (S t))) ->
 forall t, (1 <= t)%coq_nat -> (t <= limit)%coq_nat ->
 VM.find 8111 (history t) = Some (Gval (Fuint 32) (rfa_reset_word_11 inputs path)).
Proof.
 intros Steps t Lower Upper. destruct t as [|t]; [lia|].
 apply (rfa_reset_step_8111 inputs path (history t) (history t) (history (S t))).
 apply Steps;lia.
Qed.
Definition rfa_node_8112_expr := (@Eref VarOrder.T (@Eid VarOrder.T 8111)).
Definition rfa_node_8112_tail := match straight_drop 8619 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma rfa_node_8112_position : straight_drop 8618 flat_statements = Some (@Qcons VarOrder.T (@Snode VarOrder.T 8112 rfa_node_8112_expr) rfa_node_8112_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma rfa_node_8112_safe : formal_typed_suffix_safe flat_memories 8112 rfa_node_8112_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma rfa_node_8112_nonreg : has_register 8112 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem rfa_reset_step_8112 inputs path old current result :
 VM.find 8111 old = Some (Gval (Fuint 32) (rfa_reset_word_11 inputs path)) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 VM.find 8112 result = Some (Gval (Fuint 32) (rfa_reset_word_11 inputs path)).
Proof.
 intros Source Step.
 eapply formal_combinational_known_node;
 [exact rfa_node_8112_position|exact rfa_node_8112_safe|exact rfa_node_8112_nonreg| |reflexivity|exact Step].
 cbn [rfa_node_8112_expr eval_hfexpr_validif_policy eval_href_validif_policy]. exact Source.
Qed.
Theorem rfa_reset_history_8112 inputs path history limit :
 (forall t, (t < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history t) false (history t) flat_statements = Some (history (S t))) ->
 forall t, (2 <= t)%coq_nat -> (t <= limit)%coq_nat ->
 VM.find 8112 (history t) = Some (Gval (Fuint 32) (rfa_reset_word_11 inputs path)).
Proof.
 intros Steps t Lower Upper. destruct t as [|t]; [lia|].
 apply (rfa_reset_step_8112 inputs path (history t) (history t) (history (S t))).
 - apply (rfa_reset_history_8111 inputs path history limit Steps t);lia.
 - apply Steps;lia.
Qed.
Definition rfa_wire_798_decl := match straight_drop 808 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition rfa_wire_798_tail := match straight_drop 8816 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition rfa_wire_798_mid := take_statements 8007 rfa_wire_798_decl.
Lemma rfa_wire_798_position : straight_drop 807 flat_statements = Some (@Qcons VarOrder.T (@Swire VarOrder.T 798 (Gtyp (Fuint 32))) rfa_wire_798_decl).
Proof. vm_compute. reflexivity. Qed.
Lemma rfa_wire_798_split : rfa_wire_798_decl = statement_append rfa_wire_798_mid (@Qcons VarOrder.T (@Sfcnct VarOrder.T (@Eid VarOrder.T 798) (@Eref VarOrder.T (@Eid VarOrder.T 8112))) rfa_wire_798_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma rfa_wire_798_straight : straight_statements rfa_wire_798_mid.
Proof. vm_compute. exact I. Qed.
Lemma rfa_wire_798_mid_safe : formal_typed_suffix_safe flat_memories 798 rfa_wire_798_mid.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma rfa_wire_798_tail_safe : formal_typed_suffix_safe flat_memories 798 rfa_wire_798_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma rfa_wire_798_nonreg : has_register 798 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem rfa_reset_step_798 inputs path old current result :
 VM.find 8112 old = Some (Gval (Fuint 32) (rfa_reset_word_11 inputs path)) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 VM.find 798 result = Some (Gval (Fuint 32) (rfa_reset_word_11 inputs path)).
Proof.
 intros Source Step.
 apply (declared_connection_value 807 flat_statements rfa_wire_798_decl rfa_wire_798_mid rfa_wire_798_tail 798 8112 32
 (Gval (Fuint 32) (rfa_reset_word_11 inputs path)) (Gval (Fuint 32) (rfa_reset_word_11 inputs path))
 (formal_invalid_policy inputs path) flat_memories old current result rfa_wire_798_position rfa_wire_798_split rfa_wire_798_straight rfa_wire_798_mid_safe rfa_wire_798_tail_safe rfa_wire_798_nonreg (Logic.eq_refl _) Source).
 - assert (Take : take 32 (rfa_reset_word_11 inputs path) = rfa_reset_word_11 inputs path).
   { apply take_oversize. rewrite rfa_reset_word_11_size. reflexivity. }
   cbn [adapt_hvalue_as_type]. rewrite Take. unfold zext_to,zext. rewrite rfa_reset_word_11_size subnn cats0. reflexivity.
 - exact Step.
Qed.
Theorem rfa_reset_history_798 inputs path history limit :
 (forall t, (t < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history t) false (history t) flat_statements = Some (history (S t))) ->
 forall t, (3 <= t)%coq_nat -> (t <= limit)%coq_nat ->
 VM.find 798 (history t) = Some (Gval (Fuint 32) (rfa_reset_word_11 inputs path)).
Proof.
 intros Steps t Lower Upper. destruct t as [|t]; [lia|].
 apply (rfa_reset_step_798 inputs path (history t) (history t) (history (S t))).
 - apply (rfa_reset_history_8112 inputs path history limit Steps t);lia.
 - apply Steps;lia.
Qed.
Definition rfa_node_1096_expr := (@Eref VarOrder.T (@Eid VarOrder.T 798)).
Definition rfa_node_1096_tail := match straight_drop 1106 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma rfa_node_1096_position : straight_drop 1105 flat_statements = Some (@Qcons VarOrder.T (@Snode VarOrder.T 1096 rfa_node_1096_expr) rfa_node_1096_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma rfa_node_1096_safe : formal_typed_suffix_safe flat_memories 1096 rfa_node_1096_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma rfa_node_1096_nonreg : has_register 1096 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem rfa_reset_step_1096 inputs path old current result :
 VM.find 798 old = Some (Gval (Fuint 32) (rfa_reset_word_11 inputs path)) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 VM.find 1096 result = Some (Gval (Fuint 32) (rfa_reset_word_11 inputs path)).
Proof.
 intros Source Step.
 eapply formal_combinational_known_node;
 [exact rfa_node_1096_position|exact rfa_node_1096_safe|exact rfa_node_1096_nonreg| |reflexivity|exact Step].
 cbn [rfa_node_1096_expr eval_hfexpr_validif_policy eval_href_validif_policy]. exact Source.
Qed.
Theorem rfa_reset_history_1096 inputs path history limit :
 (forall t, (t < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history t) false (history t) flat_statements = Some (history (S t))) ->
 forall t, (4 <= t)%coq_nat -> (t <= limit)%coq_nat ->
 VM.find 1096 (history t) = Some (Gval (Fuint 32) (rfa_reset_word_11 inputs path)).
Proof.
 intros Steps t Lower Upper. destruct t as [|t]; [lia|].
 apply (rfa_reset_step_1096 inputs path (history t) (history t) (history (S t))).
 - apply (rfa_reset_history_798 inputs path history limit Steps t);lia.
 - apply Steps;lia.
Qed.
Definition rfa_wire_1493_decl := match straight_drop 1573 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition rfa_wire_1493_tail := match straight_drop 8982 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition rfa_wire_1493_mid := take_statements 7408 rfa_wire_1493_decl.
Lemma rfa_wire_1493_position : straight_drop 1572 flat_statements = Some (@Qcons VarOrder.T (@Swire VarOrder.T 1493 (Gtyp (Fuint 32))) rfa_wire_1493_decl).
Proof. vm_compute. reflexivity. Qed.
Lemma rfa_wire_1493_split : rfa_wire_1493_decl = statement_append rfa_wire_1493_mid (@Qcons VarOrder.T (@Sfcnct VarOrder.T (@Eid VarOrder.T 1493) (@Eref VarOrder.T (@Eid VarOrder.T 8112))) rfa_wire_1493_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma rfa_wire_1493_straight : straight_statements rfa_wire_1493_mid.
Proof. vm_compute. exact I. Qed.
Lemma rfa_wire_1493_mid_safe : formal_typed_suffix_safe flat_memories 1493 rfa_wire_1493_mid.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma rfa_wire_1493_tail_safe : formal_typed_suffix_safe flat_memories 1493 rfa_wire_1493_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma rfa_wire_1493_nonreg : has_register 1493 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem rfa_reset_step_1493 inputs path old current result :
 VM.find 8112 old = Some (Gval (Fuint 32) (rfa_reset_word_11 inputs path)) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 VM.find 1493 result = Some (Gval (Fuint 32) (rfa_reset_word_11 inputs path)).
Proof.
 intros Source Step.
 apply (declared_connection_value 1572 flat_statements rfa_wire_1493_decl rfa_wire_1493_mid rfa_wire_1493_tail 1493 8112 32
 (Gval (Fuint 32) (rfa_reset_word_11 inputs path)) (Gval (Fuint 32) (rfa_reset_word_11 inputs path))
 (formal_invalid_policy inputs path) flat_memories old current result rfa_wire_1493_position rfa_wire_1493_split rfa_wire_1493_straight rfa_wire_1493_mid_safe rfa_wire_1493_tail_safe rfa_wire_1493_nonreg (Logic.eq_refl _) Source).
 - assert (Take : take 32 (rfa_reset_word_11 inputs path) = rfa_reset_word_11 inputs path).
   { apply take_oversize. rewrite rfa_reset_word_11_size. reflexivity. }
   cbn [adapt_hvalue_as_type]. rewrite Take. unfold zext_to,zext. rewrite rfa_reset_word_11_size subnn cats0. reflexivity.
 - exact Step.
Qed.
Theorem rfa_reset_history_1493 inputs path history limit :
 (forall t, (t < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history t) false (history t) flat_statements = Some (history (S t))) ->
 forall t, (3 <= t)%coq_nat -> (t <= limit)%coq_nat ->
 VM.find 1493 (history t) = Some (Gval (Fuint 32) (rfa_reset_word_11 inputs path)).
Proof.
 intros Steps t Lower Upper. destruct t as [|t]; [lia|].
 apply (rfa_reset_step_1493 inputs path (history t) (history t) (history (S t))).
 - apply (rfa_reset_history_8112 inputs path history limit Steps t);lia.
 - apply Steps;lia.
Qed.
Definition rfa_wire_1683_decl := match straight_drop 1763 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition rfa_wire_1683_tail := match straight_drop 8234 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition rfa_wire_1683_mid := take_statements 6470 rfa_wire_1683_decl.
Lemma rfa_wire_1683_position : straight_drop 1762 flat_statements = Some (@Qcons VarOrder.T (@Swire VarOrder.T 1683 (Gtyp (Fuint 32))) rfa_wire_1683_decl).
Proof. vm_compute. reflexivity. Qed.
Lemma rfa_wire_1683_split : rfa_wire_1683_decl = statement_append rfa_wire_1683_mid (@Qcons VarOrder.T (@Sfcnct VarOrder.T (@Eid VarOrder.T 1683) (@Eref VarOrder.T (@Eid VarOrder.T 1493))) rfa_wire_1683_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma rfa_wire_1683_straight : straight_statements rfa_wire_1683_mid.
Proof. vm_compute. exact I. Qed.
Lemma rfa_wire_1683_mid_safe : formal_typed_suffix_safe flat_memories 1683 rfa_wire_1683_mid.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma rfa_wire_1683_tail_safe : formal_typed_suffix_safe flat_memories 1683 rfa_wire_1683_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma rfa_wire_1683_nonreg : has_register 1683 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem rfa_reset_step_1683 inputs path old current result :
 VM.find 1493 old = Some (Gval (Fuint 32) (rfa_reset_word_11 inputs path)) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 VM.find 1683 result = Some (Gval (Fuint 32) (rfa_reset_word_11 inputs path)).
Proof.
 intros Source Step.
 apply (declared_connection_value 1762 flat_statements rfa_wire_1683_decl rfa_wire_1683_mid rfa_wire_1683_tail 1683 1493 32
 (Gval (Fuint 32) (rfa_reset_word_11 inputs path)) (Gval (Fuint 32) (rfa_reset_word_11 inputs path))
 (formal_invalid_policy inputs path) flat_memories old current result rfa_wire_1683_position rfa_wire_1683_split rfa_wire_1683_straight rfa_wire_1683_mid_safe rfa_wire_1683_tail_safe rfa_wire_1683_nonreg (Logic.eq_refl _) Source).
 - assert (Take : take 32 (rfa_reset_word_11 inputs path) = rfa_reset_word_11 inputs path).
   { apply take_oversize. rewrite rfa_reset_word_11_size. reflexivity. }
   cbn [adapt_hvalue_as_type]. rewrite Take. unfold zext_to,zext. rewrite rfa_reset_word_11_size subnn cats0. reflexivity.
 - exact Step.
Qed.
Theorem rfa_reset_history_1683 inputs path history limit :
 (forall t, (t < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history t) false (history t) flat_statements = Some (history (S t))) ->
 forall t, (4 <= t)%coq_nat -> (t <= limit)%coq_nat ->
 VM.find 1683 (history t) = Some (Gval (Fuint 32) (rfa_reset_word_11 inputs path)).
Proof.
 intros Steps t Lower Upper. destruct t as [|t]; [lia|].
 apply (rfa_reset_step_1683 inputs path (history t) (history t) (history (S t))).
 - apply (rfa_reset_history_1493 inputs path history limit Steps t);lia.
 - apply Steps;lia.
Qed.
Definition rfa_node_7391_expr := (@Eref VarOrder.T (@Eid VarOrder.T 1683)).
Definition rfa_node_7391_tail := match straight_drop 7563 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma rfa_node_7391_position : straight_drop 7562 flat_statements = Some (@Qcons VarOrder.T (@Snode VarOrder.T 7391 rfa_node_7391_expr) rfa_node_7391_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma rfa_node_7391_safe : formal_typed_suffix_safe flat_memories 7391 rfa_node_7391_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma rfa_node_7391_nonreg : has_register 7391 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem rfa_reset_step_7391 inputs path old current result :
 VM.find 1683 old = Some (Gval (Fuint 32) (rfa_reset_word_11 inputs path)) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 VM.find 7391 result = Some (Gval (Fuint 32) (rfa_reset_word_11 inputs path)).
Proof.
 intros Source Step.
 eapply formal_combinational_known_node;
 [exact rfa_node_7391_position|exact rfa_node_7391_safe|exact rfa_node_7391_nonreg| |reflexivity|exact Step].
 cbn [rfa_node_7391_expr eval_hfexpr_validif_policy eval_href_validif_policy]. exact Source.
Qed.
Theorem rfa_reset_history_7391 inputs path history limit :
 (forall t, (t < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history t) false (history t) flat_statements = Some (history (S t))) ->
 forall t, (5 <= t)%coq_nat -> (t <= limit)%coq_nat ->
 VM.find 7391 (history t) = Some (Gval (Fuint 32) (rfa_reset_word_11 inputs path)).
Proof.
 intros Steps t Lower Upper. destruct t as [|t]; [lia|].
 apply (rfa_reset_step_7391 inputs path (history t) (history t) (history (S t))).
 - apply (rfa_reset_history_1683 inputs path history limit Steps t);lia.
 - apply Steps;lia.
Qed.
Definition rfa_node_7392_expr := (@Eref VarOrder.T (@Eid VarOrder.T 7391)).
Definition rfa_node_7392_tail := match straight_drop 7564 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma rfa_node_7392_position : straight_drop 7563 flat_statements = Some (@Qcons VarOrder.T (@Snode VarOrder.T 7392 rfa_node_7392_expr) rfa_node_7392_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma rfa_node_7392_safe : formal_typed_suffix_safe flat_memories 7392 rfa_node_7392_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma rfa_node_7392_nonreg : has_register 7392 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem rfa_reset_step_7392 inputs path old current result :
 VM.find 7391 old = Some (Gval (Fuint 32) (rfa_reset_word_11 inputs path)) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 VM.find 7392 result = Some (Gval (Fuint 32) (rfa_reset_word_11 inputs path)).
Proof.
 intros Source Step.
 eapply formal_combinational_known_node;
 [exact rfa_node_7392_position|exact rfa_node_7392_safe|exact rfa_node_7392_nonreg| |reflexivity|exact Step].
 cbn [rfa_node_7392_expr eval_hfexpr_validif_policy eval_href_validif_policy]. exact Source.
Qed.
Theorem rfa_reset_history_7392 inputs path history limit :
 (forall t, (t < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history t) false (history t) flat_statements = Some (history (S t))) ->
 forall t, (6 <= t)%coq_nat -> (t <= limit)%coq_nat ->
 VM.find 7392 (history t) = Some (Gval (Fuint 32) (rfa_reset_word_11 inputs path)).
Proof.
 intros Steps t Lower Upper. destruct t as [|t]; [lia|].
 apply (rfa_reset_step_7392 inputs path (history t) (history t) (history (S t))).
 - apply (rfa_reset_history_7391 inputs path history limit Steps t);lia.
 - apply Steps;lia.
Qed.
