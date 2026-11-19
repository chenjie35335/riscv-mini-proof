Require Import CoreSocModel ComparisonNodes ScalarNodeFrames FormalTypedNodeFrames RegisterInvariants FormalTypedNodeEquation FormalDeclaredConnection FormalStatementSegments RegisterCommitCertificate FormalUIntRegisterCommitSource SelectedUIntMuxIdentity UIntResizeRoundtrip.
From Coq Require Import ZArith List Lia.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From nbits Require Import NBits.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Definition rfa_reset_word_4 inputs path := proj1_sig (formal_symbolic_inputs inputs path (validif_source_address (validif_raw_address nil 8603 0 nil)) nil 32).
Lemma rfa_reset_word_4_size inputs path : size (rfa_reset_word_4 inputs path) = 32%nat.
Proof. exact (proj2_sig (formal_symbolic_inputs inputs path (validif_source_address (validif_raw_address nil 8603 0 nil)) nil 32)). Qed.
Definition rfa_node_8097_expr := (@Evalidif VarOrder.T (@Econst VarOrder.T (Fuint 1) [::false]) (@Econst VarOrder.T (Fuint 32) [::false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false])).
Definition rfa_node_8097_tail := match straight_drop 8604 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma rfa_node_8097_position : straight_drop 8603 flat_statements = Some (@Qcons VarOrder.T (@Snode VarOrder.T 8097 rfa_node_8097_expr) rfa_node_8097_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma rfa_node_8097_safe : formal_typed_suffix_safe flat_memories 8097 rfa_node_8097_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma rfa_node_8097_nonreg : has_register 8097 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem rfa_reset_step_8097 inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 VM.find 8097 result = Some (Gval (Fuint 32) (rfa_reset_word_4 inputs path)).
Proof.
 intros Step.
 eapply formal_combinational_known_node;
 [exact rfa_node_8097_position|exact rfa_node_8097_safe|exact rfa_node_8097_nonreg| |reflexivity|exact Step].
 reflexivity.
Qed.
Theorem rfa_reset_history_8097 inputs path history limit :
 (forall t, (t < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history t) false (history t) flat_statements = Some (history (S t))) ->
 forall t, (1 <= t)%coq_nat -> (t <= limit)%coq_nat ->
 VM.find 8097 (history t) = Some (Gval (Fuint 32) (rfa_reset_word_4 inputs path)).
Proof.
 intros Steps t Lower Upper. destruct t as [|t]; [lia|].
 apply (rfa_reset_step_8097 inputs path (history t) (history t) (history (S t))).
 apply Steps;lia.
Qed.
Definition rfa_node_8098_expr := (@Eref VarOrder.T (@Eid VarOrder.T 8097)).
Definition rfa_node_8098_tail := match straight_drop 8605 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma rfa_node_8098_position : straight_drop 8604 flat_statements = Some (@Qcons VarOrder.T (@Snode VarOrder.T 8098 rfa_node_8098_expr) rfa_node_8098_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma rfa_node_8098_safe : formal_typed_suffix_safe flat_memories 8098 rfa_node_8098_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma rfa_node_8098_nonreg : has_register 8098 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem rfa_reset_step_8098 inputs path old current result :
 VM.find 8097 old = Some (Gval (Fuint 32) (rfa_reset_word_4 inputs path)) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 VM.find 8098 result = Some (Gval (Fuint 32) (rfa_reset_word_4 inputs path)).
Proof.
 intros Source Step.
 eapply formal_combinational_known_node;
 [exact rfa_node_8098_position|exact rfa_node_8098_safe|exact rfa_node_8098_nonreg| |reflexivity|exact Step].
 cbn [rfa_node_8098_expr eval_hfexpr_validif_policy eval_href_validif_policy]. exact Source.
Qed.
Theorem rfa_reset_history_8098 inputs path history limit :
 (forall t, (t < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history t) false (history t) flat_statements = Some (history (S t))) ->
 forall t, (2 <= t)%coq_nat -> (t <= limit)%coq_nat ->
 VM.find 8098 (history t) = Some (Gval (Fuint 32) (rfa_reset_word_4 inputs path)).
Proof.
 intros Steps t Lower Upper. destruct t as [|t]; [lia|].
 apply (rfa_reset_step_8098 inputs path (history t) (history t) (history (S t))).
 - apply (rfa_reset_history_8097 inputs path history limit Steps t);lia.
 - apply Steps;lia.
Qed.
Definition rfa_wire_791_decl := match straight_drop 801 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition rfa_wire_791_tail := match straight_drop 8809 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition rfa_wire_791_mid := take_statements 8007 rfa_wire_791_decl.
Lemma rfa_wire_791_position : straight_drop 800 flat_statements = Some (@Qcons VarOrder.T (@Swire VarOrder.T 791 (Gtyp (Fuint 32))) rfa_wire_791_decl).
Proof. vm_compute. reflexivity. Qed.
Lemma rfa_wire_791_split : rfa_wire_791_decl = statement_append rfa_wire_791_mid (@Qcons VarOrder.T (@Sfcnct VarOrder.T (@Eid VarOrder.T 791) (@Eref VarOrder.T (@Eid VarOrder.T 8098))) rfa_wire_791_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma rfa_wire_791_straight : straight_statements rfa_wire_791_mid.
Proof. vm_compute. exact I. Qed.
Lemma rfa_wire_791_mid_safe : formal_typed_suffix_safe flat_memories 791 rfa_wire_791_mid.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma rfa_wire_791_tail_safe : formal_typed_suffix_safe flat_memories 791 rfa_wire_791_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma rfa_wire_791_nonreg : has_register 791 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem rfa_reset_step_791 inputs path old current result :
 VM.find 8098 old = Some (Gval (Fuint 32) (rfa_reset_word_4 inputs path)) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 VM.find 791 result = Some (Gval (Fuint 32) (rfa_reset_word_4 inputs path)).
Proof.
 intros Source Step.
 apply (declared_connection_value 800 flat_statements rfa_wire_791_decl rfa_wire_791_mid rfa_wire_791_tail 791 8098 32
 (Gval (Fuint 32) (rfa_reset_word_4 inputs path)) (Gval (Fuint 32) (rfa_reset_word_4 inputs path))
 (formal_invalid_policy inputs path) flat_memories old current result rfa_wire_791_position rfa_wire_791_split rfa_wire_791_straight rfa_wire_791_mid_safe rfa_wire_791_tail_safe rfa_wire_791_nonreg (Logic.eq_refl _) Source).
 - assert (Take : take 32 (rfa_reset_word_4 inputs path) = rfa_reset_word_4 inputs path).
   { apply take_oversize. rewrite rfa_reset_word_4_size. reflexivity. }
   cbn [adapt_hvalue_as_type]. rewrite Take. unfold zext_to,zext. rewrite rfa_reset_word_4_size subnn cats0. reflexivity.
 - exact Step.
Qed.
Theorem rfa_reset_history_791 inputs path history limit :
 (forall t, (t < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history t) false (history t) flat_statements = Some (history (S t))) ->
 forall t, (3 <= t)%coq_nat -> (t <= limit)%coq_nat ->
 VM.find 791 (history t) = Some (Gval (Fuint 32) (rfa_reset_word_4 inputs path)).
Proof.
 intros Steps t Lower Upper. destruct t as [|t]; [lia|].
 apply (rfa_reset_step_791 inputs path (history t) (history t) (history (S t))).
 - apply (rfa_reset_history_8098 inputs path history limit Steps t);lia.
 - apply Steps;lia.
Qed.
Definition rfa_node_1089_expr := (@Eref VarOrder.T (@Eid VarOrder.T 791)).
Definition rfa_node_1089_tail := match straight_drop 1099 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma rfa_node_1089_position : straight_drop 1098 flat_statements = Some (@Qcons VarOrder.T (@Snode VarOrder.T 1089 rfa_node_1089_expr) rfa_node_1089_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma rfa_node_1089_safe : formal_typed_suffix_safe flat_memories 1089 rfa_node_1089_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma rfa_node_1089_nonreg : has_register 1089 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem rfa_reset_step_1089 inputs path old current result :
 VM.find 791 old = Some (Gval (Fuint 32) (rfa_reset_word_4 inputs path)) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 VM.find 1089 result = Some (Gval (Fuint 32) (rfa_reset_word_4 inputs path)).
Proof.
 intros Source Step.
 eapply formal_combinational_known_node;
 [exact rfa_node_1089_position|exact rfa_node_1089_safe|exact rfa_node_1089_nonreg| |reflexivity|exact Step].
 cbn [rfa_node_1089_expr eval_hfexpr_validif_policy eval_href_validif_policy]. exact Source.
Qed.
Theorem rfa_reset_history_1089 inputs path history limit :
 (forall t, (t < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history t) false (history t) flat_statements = Some (history (S t))) ->
 forall t, (4 <= t)%coq_nat -> (t <= limit)%coq_nat ->
 VM.find 1089 (history t) = Some (Gval (Fuint 32) (rfa_reset_word_4 inputs path)).
Proof.
 intros Steps t Lower Upper. destruct t as [|t]; [lia|].
 apply (rfa_reset_step_1089 inputs path (history t) (history t) (history (S t))).
 - apply (rfa_reset_history_791 inputs path history limit Steps t);lia.
 - apply Steps;lia.
Qed.
Definition rfa_wire_1486_decl := match straight_drop 1566 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition rfa_wire_1486_tail := match straight_drop 8975 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition rfa_wire_1486_mid := take_statements 7408 rfa_wire_1486_decl.
Lemma rfa_wire_1486_position : straight_drop 1565 flat_statements = Some (@Qcons VarOrder.T (@Swire VarOrder.T 1486 (Gtyp (Fuint 32))) rfa_wire_1486_decl).
Proof. vm_compute. reflexivity. Qed.
Lemma rfa_wire_1486_split : rfa_wire_1486_decl = statement_append rfa_wire_1486_mid (@Qcons VarOrder.T (@Sfcnct VarOrder.T (@Eid VarOrder.T 1486) (@Eref VarOrder.T (@Eid VarOrder.T 8098))) rfa_wire_1486_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma rfa_wire_1486_straight : straight_statements rfa_wire_1486_mid.
Proof. vm_compute. exact I. Qed.
Lemma rfa_wire_1486_mid_safe : formal_typed_suffix_safe flat_memories 1486 rfa_wire_1486_mid.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma rfa_wire_1486_tail_safe : formal_typed_suffix_safe flat_memories 1486 rfa_wire_1486_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma rfa_wire_1486_nonreg : has_register 1486 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem rfa_reset_step_1486 inputs path old current result :
 VM.find 8098 old = Some (Gval (Fuint 32) (rfa_reset_word_4 inputs path)) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 VM.find 1486 result = Some (Gval (Fuint 32) (rfa_reset_word_4 inputs path)).
Proof.
 intros Source Step.
 apply (declared_connection_value 1565 flat_statements rfa_wire_1486_decl rfa_wire_1486_mid rfa_wire_1486_tail 1486 8098 32
 (Gval (Fuint 32) (rfa_reset_word_4 inputs path)) (Gval (Fuint 32) (rfa_reset_word_4 inputs path))
 (formal_invalid_policy inputs path) flat_memories old current result rfa_wire_1486_position rfa_wire_1486_split rfa_wire_1486_straight rfa_wire_1486_mid_safe rfa_wire_1486_tail_safe rfa_wire_1486_nonreg (Logic.eq_refl _) Source).
 - assert (Take : take 32 (rfa_reset_word_4 inputs path) = rfa_reset_word_4 inputs path).
   { apply take_oversize. rewrite rfa_reset_word_4_size. reflexivity. }
   cbn [adapt_hvalue_as_type]. rewrite Take. unfold zext_to,zext. rewrite rfa_reset_word_4_size subnn cats0. reflexivity.
 - exact Step.
Qed.
Theorem rfa_reset_history_1486 inputs path history limit :
 (forall t, (t < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history t) false (history t) flat_statements = Some (history (S t))) ->
 forall t, (3 <= t)%coq_nat -> (t <= limit)%coq_nat ->
 VM.find 1486 (history t) = Some (Gval (Fuint 32) (rfa_reset_word_4 inputs path)).
Proof.
 intros Steps t Lower Upper. destruct t as [|t]; [lia|].
 apply (rfa_reset_step_1486 inputs path (history t) (history t) (history (S t))).
 - apply (rfa_reset_history_8098 inputs path history limit Steps t);lia.
 - apply Steps;lia.
Qed.
Definition rfa_wire_1676_decl := match straight_drop 1756 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition rfa_wire_1676_tail := match straight_drop 8227 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition rfa_wire_1676_mid := take_statements 6470 rfa_wire_1676_decl.
Lemma rfa_wire_1676_position : straight_drop 1755 flat_statements = Some (@Qcons VarOrder.T (@Swire VarOrder.T 1676 (Gtyp (Fuint 32))) rfa_wire_1676_decl).
Proof. vm_compute. reflexivity. Qed.
Lemma rfa_wire_1676_split : rfa_wire_1676_decl = statement_append rfa_wire_1676_mid (@Qcons VarOrder.T (@Sfcnct VarOrder.T (@Eid VarOrder.T 1676) (@Eref VarOrder.T (@Eid VarOrder.T 1486))) rfa_wire_1676_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma rfa_wire_1676_straight : straight_statements rfa_wire_1676_mid.
Proof. vm_compute. exact I. Qed.
Lemma rfa_wire_1676_mid_safe : formal_typed_suffix_safe flat_memories 1676 rfa_wire_1676_mid.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma rfa_wire_1676_tail_safe : formal_typed_suffix_safe flat_memories 1676 rfa_wire_1676_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma rfa_wire_1676_nonreg : has_register 1676 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem rfa_reset_step_1676 inputs path old current result :
 VM.find 1486 old = Some (Gval (Fuint 32) (rfa_reset_word_4 inputs path)) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 VM.find 1676 result = Some (Gval (Fuint 32) (rfa_reset_word_4 inputs path)).
Proof.
 intros Source Step.
 apply (declared_connection_value 1755 flat_statements rfa_wire_1676_decl rfa_wire_1676_mid rfa_wire_1676_tail 1676 1486 32
 (Gval (Fuint 32) (rfa_reset_word_4 inputs path)) (Gval (Fuint 32) (rfa_reset_word_4 inputs path))
 (formal_invalid_policy inputs path) flat_memories old current result rfa_wire_1676_position rfa_wire_1676_split rfa_wire_1676_straight rfa_wire_1676_mid_safe rfa_wire_1676_tail_safe rfa_wire_1676_nonreg (Logic.eq_refl _) Source).
 - assert (Take : take 32 (rfa_reset_word_4 inputs path) = rfa_reset_word_4 inputs path).
   { apply take_oversize. rewrite rfa_reset_word_4_size. reflexivity. }
   cbn [adapt_hvalue_as_type]. rewrite Take. unfold zext_to,zext. rewrite rfa_reset_word_4_size subnn cats0. reflexivity.
 - exact Step.
Qed.
Theorem rfa_reset_history_1676 inputs path history limit :
 (forall t, (t < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history t) false (history t) flat_statements = Some (history (S t))) ->
 forall t, (4 <= t)%coq_nat -> (t <= limit)%coq_nat ->
 VM.find 1676 (history t) = Some (Gval (Fuint 32) (rfa_reset_word_4 inputs path)).
Proof.
 intros Steps t Lower Upper. destruct t as [|t]; [lia|].
 apply (rfa_reset_step_1676 inputs path (history t) (history t) (history (S t))).
 - apply (rfa_reset_history_1486 inputs path history limit Steps t);lia.
 - apply Steps;lia.
Qed.
Definition rfa_node_7377_expr := (@Eref VarOrder.T (@Eid VarOrder.T 1676)).
Definition rfa_node_7377_tail := match straight_drop 7549 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma rfa_node_7377_position : straight_drop 7548 flat_statements = Some (@Qcons VarOrder.T (@Snode VarOrder.T 7377 rfa_node_7377_expr) rfa_node_7377_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma rfa_node_7377_safe : formal_typed_suffix_safe flat_memories 7377 rfa_node_7377_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma rfa_node_7377_nonreg : has_register 7377 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem rfa_reset_step_7377 inputs path old current result :
 VM.find 1676 old = Some (Gval (Fuint 32) (rfa_reset_word_4 inputs path)) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 VM.find 7377 result = Some (Gval (Fuint 32) (rfa_reset_word_4 inputs path)).
Proof.
 intros Source Step.
 eapply formal_combinational_known_node;
 [exact rfa_node_7377_position|exact rfa_node_7377_safe|exact rfa_node_7377_nonreg| |reflexivity|exact Step].
 cbn [rfa_node_7377_expr eval_hfexpr_validif_policy eval_href_validif_policy]. exact Source.
Qed.
Theorem rfa_reset_history_7377 inputs path history limit :
 (forall t, (t < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history t) false (history t) flat_statements = Some (history (S t))) ->
 forall t, (5 <= t)%coq_nat -> (t <= limit)%coq_nat ->
 VM.find 7377 (history t) = Some (Gval (Fuint 32) (rfa_reset_word_4 inputs path)).
Proof.
 intros Steps t Lower Upper. destruct t as [|t]; [lia|].
 apply (rfa_reset_step_7377 inputs path (history t) (history t) (history (S t))).
 - apply (rfa_reset_history_1676 inputs path history limit Steps t);lia.
 - apply Steps;lia.
Qed.
Definition rfa_node_7378_expr := (@Eref VarOrder.T (@Eid VarOrder.T 7377)).
Definition rfa_node_7378_tail := match straight_drop 7550 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma rfa_node_7378_position : straight_drop 7549 flat_statements = Some (@Qcons VarOrder.T (@Snode VarOrder.T 7378 rfa_node_7378_expr) rfa_node_7378_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma rfa_node_7378_safe : formal_typed_suffix_safe flat_memories 7378 rfa_node_7378_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma rfa_node_7378_nonreg : has_register 7378 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem rfa_reset_step_7378 inputs path old current result :
 VM.find 7377 old = Some (Gval (Fuint 32) (rfa_reset_word_4 inputs path)) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 VM.find 7378 result = Some (Gval (Fuint 32) (rfa_reset_word_4 inputs path)).
Proof.
 intros Source Step.
 eapply formal_combinational_known_node;
 [exact rfa_node_7378_position|exact rfa_node_7378_safe|exact rfa_node_7378_nonreg| |reflexivity|exact Step].
 cbn [rfa_node_7378_expr eval_hfexpr_validif_policy eval_href_validif_policy]. exact Source.
Qed.
Theorem rfa_reset_history_7378 inputs path history limit :
 (forall t, (t < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history t) false (history t) flat_statements = Some (history (S t))) ->
 forall t, (6 <= t)%coq_nat -> (t <= limit)%coq_nat ->
 VM.find 7378 (history t) = Some (Gval (Fuint 32) (rfa_reset_word_4 inputs path)).
Proof.
 intros Steps t Lower Upper. destruct t as [|t]; [lia|].
 apply (rfa_reset_step_7378 inputs path (history t) (history t) (history (S t))).
 - apply (rfa_reset_history_7377 inputs path history limit Steps t);lia.
 - apply Steps;lia.
Qed.
Definition rfa_reset_word_5 inputs path := proj1_sig (formal_symbolic_inputs inputs path (validif_source_address (validif_raw_address nil 8605 0 nil)) nil 32).
Lemma rfa_reset_word_5_size inputs path : size (rfa_reset_word_5 inputs path) = 32%nat.
Proof. exact (proj2_sig (formal_symbolic_inputs inputs path (validif_source_address (validif_raw_address nil 8605 0 nil)) nil 32)). Qed.
Definition rfa_node_8099_expr := (@Evalidif VarOrder.T (@Econst VarOrder.T (Fuint 1) [::false]) (@Econst VarOrder.T (Fuint 32) [::false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false])).
Definition rfa_node_8099_tail := match straight_drop 8606 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma rfa_node_8099_position : straight_drop 8605 flat_statements = Some (@Qcons VarOrder.T (@Snode VarOrder.T 8099 rfa_node_8099_expr) rfa_node_8099_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma rfa_node_8099_safe : formal_typed_suffix_safe flat_memories 8099 rfa_node_8099_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma rfa_node_8099_nonreg : has_register 8099 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem rfa_reset_step_8099 inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 VM.find 8099 result = Some (Gval (Fuint 32) (rfa_reset_word_5 inputs path)).
Proof.
 intros Step.
 eapply formal_combinational_known_node;
 [exact rfa_node_8099_position|exact rfa_node_8099_safe|exact rfa_node_8099_nonreg| |reflexivity|exact Step].
 reflexivity.
Qed.
Theorem rfa_reset_history_8099 inputs path history limit :
 (forall t, (t < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history t) false (history t) flat_statements = Some (history (S t))) ->
 forall t, (1 <= t)%coq_nat -> (t <= limit)%coq_nat ->
 VM.find 8099 (history t) = Some (Gval (Fuint 32) (rfa_reset_word_5 inputs path)).
Proof.
 intros Steps t Lower Upper. destruct t as [|t]; [lia|].
 apply (rfa_reset_step_8099 inputs path (history t) (history t) (history (S t))).
 apply Steps;lia.
Qed.
Definition rfa_node_8100_expr := (@Eref VarOrder.T (@Eid VarOrder.T 8099)).
Definition rfa_node_8100_tail := match straight_drop 8607 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma rfa_node_8100_position : straight_drop 8606 flat_statements = Some (@Qcons VarOrder.T (@Snode VarOrder.T 8100 rfa_node_8100_expr) rfa_node_8100_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma rfa_node_8100_safe : formal_typed_suffix_safe flat_memories 8100 rfa_node_8100_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma rfa_node_8100_nonreg : has_register 8100 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem rfa_reset_step_8100 inputs path old current result :
 VM.find 8099 old = Some (Gval (Fuint 32) (rfa_reset_word_5 inputs path)) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 VM.find 8100 result = Some (Gval (Fuint 32) (rfa_reset_word_5 inputs path)).
Proof.
 intros Source Step.
 eapply formal_combinational_known_node;
 [exact rfa_node_8100_position|exact rfa_node_8100_safe|exact rfa_node_8100_nonreg| |reflexivity|exact Step].
 cbn [rfa_node_8100_expr eval_hfexpr_validif_policy eval_href_validif_policy]. exact Source.
Qed.
Theorem rfa_reset_history_8100 inputs path history limit :
 (forall t, (t < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history t) false (history t) flat_statements = Some (history (S t))) ->
 forall t, (2 <= t)%coq_nat -> (t <= limit)%coq_nat ->
 VM.find 8100 (history t) = Some (Gval (Fuint 32) (rfa_reset_word_5 inputs path)).
Proof.
 intros Steps t Lower Upper. destruct t as [|t]; [lia|].
 apply (rfa_reset_step_8100 inputs path (history t) (history t) (history (S t))).
 - apply (rfa_reset_history_8099 inputs path history limit Steps t);lia.
 - apply Steps;lia.
Qed.
Definition rfa_wire_792_decl := match straight_drop 802 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition rfa_wire_792_tail := match straight_drop 8810 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition rfa_wire_792_mid := take_statements 8007 rfa_wire_792_decl.
Lemma rfa_wire_792_position : straight_drop 801 flat_statements = Some (@Qcons VarOrder.T (@Swire VarOrder.T 792 (Gtyp (Fuint 32))) rfa_wire_792_decl).
Proof. vm_compute. reflexivity. Qed.
Lemma rfa_wire_792_split : rfa_wire_792_decl = statement_append rfa_wire_792_mid (@Qcons VarOrder.T (@Sfcnct VarOrder.T (@Eid VarOrder.T 792) (@Eref VarOrder.T (@Eid VarOrder.T 8100))) rfa_wire_792_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma rfa_wire_792_straight : straight_statements rfa_wire_792_mid.
Proof. vm_compute. exact I. Qed.
Lemma rfa_wire_792_mid_safe : formal_typed_suffix_safe flat_memories 792 rfa_wire_792_mid.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma rfa_wire_792_tail_safe : formal_typed_suffix_safe flat_memories 792 rfa_wire_792_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma rfa_wire_792_nonreg : has_register 792 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem rfa_reset_step_792 inputs path old current result :
 VM.find 8100 old = Some (Gval (Fuint 32) (rfa_reset_word_5 inputs path)) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 VM.find 792 result = Some (Gval (Fuint 32) (rfa_reset_word_5 inputs path)).
Proof.
 intros Source Step.
 apply (declared_connection_value 801 flat_statements rfa_wire_792_decl rfa_wire_792_mid rfa_wire_792_tail 792 8100 32
 (Gval (Fuint 32) (rfa_reset_word_5 inputs path)) (Gval (Fuint 32) (rfa_reset_word_5 inputs path))
 (formal_invalid_policy inputs path) flat_memories old current result rfa_wire_792_position rfa_wire_792_split rfa_wire_792_straight rfa_wire_792_mid_safe rfa_wire_792_tail_safe rfa_wire_792_nonreg (Logic.eq_refl _) Source).
 - assert (Take : take 32 (rfa_reset_word_5 inputs path) = rfa_reset_word_5 inputs path).
   { apply take_oversize. rewrite rfa_reset_word_5_size. reflexivity. }
   cbn [adapt_hvalue_as_type]. rewrite Take. unfold zext_to,zext. rewrite rfa_reset_word_5_size subnn cats0. reflexivity.
 - exact Step.
Qed.
Theorem rfa_reset_history_792 inputs path history limit :
 (forall t, (t < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history t) false (history t) flat_statements = Some (history (S t))) ->
 forall t, (3 <= t)%coq_nat -> (t <= limit)%coq_nat ->
 VM.find 792 (history t) = Some (Gval (Fuint 32) (rfa_reset_word_5 inputs path)).
Proof.
 intros Steps t Lower Upper. destruct t as [|t]; [lia|].
 apply (rfa_reset_step_792 inputs path (history t) (history t) (history (S t))).
 - apply (rfa_reset_history_8100 inputs path history limit Steps t);lia.
 - apply Steps;lia.
Qed.
Definition rfa_node_1090_expr := (@Eref VarOrder.T (@Eid VarOrder.T 792)).
Definition rfa_node_1090_tail := match straight_drop 1100 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma rfa_node_1090_position : straight_drop 1099 flat_statements = Some (@Qcons VarOrder.T (@Snode VarOrder.T 1090 rfa_node_1090_expr) rfa_node_1090_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma rfa_node_1090_safe : formal_typed_suffix_safe flat_memories 1090 rfa_node_1090_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma rfa_node_1090_nonreg : has_register 1090 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem rfa_reset_step_1090 inputs path old current result :
 VM.find 792 old = Some (Gval (Fuint 32) (rfa_reset_word_5 inputs path)) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 VM.find 1090 result = Some (Gval (Fuint 32) (rfa_reset_word_5 inputs path)).
Proof.
 intros Source Step.
 eapply formal_combinational_known_node;
 [exact rfa_node_1090_position|exact rfa_node_1090_safe|exact rfa_node_1090_nonreg| |reflexivity|exact Step].
 cbn [rfa_node_1090_expr eval_hfexpr_validif_policy eval_href_validif_policy]. exact Source.
Qed.
Theorem rfa_reset_history_1090 inputs path history limit :
 (forall t, (t < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history t) false (history t) flat_statements = Some (history (S t))) ->
 forall t, (4 <= t)%coq_nat -> (t <= limit)%coq_nat ->
 VM.find 1090 (history t) = Some (Gval (Fuint 32) (rfa_reset_word_5 inputs path)).
Proof.
 intros Steps t Lower Upper. destruct t as [|t]; [lia|].
 apply (rfa_reset_step_1090 inputs path (history t) (history t) (history (S t))).
 - apply (rfa_reset_history_792 inputs path history limit Steps t);lia.
 - apply Steps;lia.
Qed.
Definition rfa_wire_1487_decl := match straight_drop 1567 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition rfa_wire_1487_tail := match straight_drop 8976 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition rfa_wire_1487_mid := take_statements 7408 rfa_wire_1487_decl.
Lemma rfa_wire_1487_position : straight_drop 1566 flat_statements = Some (@Qcons VarOrder.T (@Swire VarOrder.T 1487 (Gtyp (Fuint 32))) rfa_wire_1487_decl).
Proof. vm_compute. reflexivity. Qed.
Lemma rfa_wire_1487_split : rfa_wire_1487_decl = statement_append rfa_wire_1487_mid (@Qcons VarOrder.T (@Sfcnct VarOrder.T (@Eid VarOrder.T 1487) (@Eref VarOrder.T (@Eid VarOrder.T 8100))) rfa_wire_1487_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma rfa_wire_1487_straight : straight_statements rfa_wire_1487_mid.
Proof. vm_compute. exact I. Qed.
Lemma rfa_wire_1487_mid_safe : formal_typed_suffix_safe flat_memories 1487 rfa_wire_1487_mid.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma rfa_wire_1487_tail_safe : formal_typed_suffix_safe flat_memories 1487 rfa_wire_1487_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma rfa_wire_1487_nonreg : has_register 1487 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem rfa_reset_step_1487 inputs path old current result :
 VM.find 8100 old = Some (Gval (Fuint 32) (rfa_reset_word_5 inputs path)) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 VM.find 1487 result = Some (Gval (Fuint 32) (rfa_reset_word_5 inputs path)).
Proof.
 intros Source Step.
 apply (declared_connection_value 1566 flat_statements rfa_wire_1487_decl rfa_wire_1487_mid rfa_wire_1487_tail 1487 8100 32
 (Gval (Fuint 32) (rfa_reset_word_5 inputs path)) (Gval (Fuint 32) (rfa_reset_word_5 inputs path))
 (formal_invalid_policy inputs path) flat_memories old current result rfa_wire_1487_position rfa_wire_1487_split rfa_wire_1487_straight rfa_wire_1487_mid_safe rfa_wire_1487_tail_safe rfa_wire_1487_nonreg (Logic.eq_refl _) Source).
 - assert (Take : take 32 (rfa_reset_word_5 inputs path) = rfa_reset_word_5 inputs path).
   { apply take_oversize. rewrite rfa_reset_word_5_size. reflexivity. }
   cbn [adapt_hvalue_as_type]. rewrite Take. unfold zext_to,zext. rewrite rfa_reset_word_5_size subnn cats0. reflexivity.
 - exact Step.
Qed.
Theorem rfa_reset_history_1487 inputs path history limit :
 (forall t, (t < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history t) false (history t) flat_statements = Some (history (S t))) ->
 forall t, (3 <= t)%coq_nat -> (t <= limit)%coq_nat ->
 VM.find 1487 (history t) = Some (Gval (Fuint 32) (rfa_reset_word_5 inputs path)).
Proof.
 intros Steps t Lower Upper. destruct t as [|t]; [lia|].
 apply (rfa_reset_step_1487 inputs path (history t) (history t) (history (S t))).
 - apply (rfa_reset_history_8100 inputs path history limit Steps t);lia.
 - apply Steps;lia.
Qed.
Definition rfa_wire_1677_decl := match straight_drop 1757 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition rfa_wire_1677_tail := match straight_drop 8228 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition rfa_wire_1677_mid := take_statements 6470 rfa_wire_1677_decl.
Lemma rfa_wire_1677_position : straight_drop 1756 flat_statements = Some (@Qcons VarOrder.T (@Swire VarOrder.T 1677 (Gtyp (Fuint 32))) rfa_wire_1677_decl).
Proof. vm_compute. reflexivity. Qed.
Lemma rfa_wire_1677_split : rfa_wire_1677_decl = statement_append rfa_wire_1677_mid (@Qcons VarOrder.T (@Sfcnct VarOrder.T (@Eid VarOrder.T 1677) (@Eref VarOrder.T (@Eid VarOrder.T 1487))) rfa_wire_1677_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma rfa_wire_1677_straight : straight_statements rfa_wire_1677_mid.
Proof. vm_compute. exact I. Qed.
Lemma rfa_wire_1677_mid_safe : formal_typed_suffix_safe flat_memories 1677 rfa_wire_1677_mid.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma rfa_wire_1677_tail_safe : formal_typed_suffix_safe flat_memories 1677 rfa_wire_1677_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma rfa_wire_1677_nonreg : has_register 1677 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem rfa_reset_step_1677 inputs path old current result :
 VM.find 1487 old = Some (Gval (Fuint 32) (rfa_reset_word_5 inputs path)) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 VM.find 1677 result = Some (Gval (Fuint 32) (rfa_reset_word_5 inputs path)).
Proof.
 intros Source Step.
 apply (declared_connection_value 1756 flat_statements rfa_wire_1677_decl rfa_wire_1677_mid rfa_wire_1677_tail 1677 1487 32
 (Gval (Fuint 32) (rfa_reset_word_5 inputs path)) (Gval (Fuint 32) (rfa_reset_word_5 inputs path))
 (formal_invalid_policy inputs path) flat_memories old current result rfa_wire_1677_position rfa_wire_1677_split rfa_wire_1677_straight rfa_wire_1677_mid_safe rfa_wire_1677_tail_safe rfa_wire_1677_nonreg (Logic.eq_refl _) Source).
 - assert (Take : take 32 (rfa_reset_word_5 inputs path) = rfa_reset_word_5 inputs path).
   { apply take_oversize. rewrite rfa_reset_word_5_size. reflexivity. }
   cbn [adapt_hvalue_as_type]. rewrite Take. unfold zext_to,zext. rewrite rfa_reset_word_5_size subnn cats0. reflexivity.
 - exact Step.
Qed.
Theorem rfa_reset_history_1677 inputs path history limit :
 (forall t, (t < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history t) false (history t) flat_statements = Some (history (S t))) ->
 forall t, (4 <= t)%coq_nat -> (t <= limit)%coq_nat ->
 VM.find 1677 (history t) = Some (Gval (Fuint 32) (rfa_reset_word_5 inputs path)).
Proof.
 intros Steps t Lower Upper. destruct t as [|t]; [lia|].
 apply (rfa_reset_step_1677 inputs path (history t) (history t) (history (S t))).
 - apply (rfa_reset_history_1487 inputs path history limit Steps t);lia.
 - apply Steps;lia.
Qed.
Definition rfa_node_7379_expr := (@Eref VarOrder.T (@Eid VarOrder.T 1677)).
Definition rfa_node_7379_tail := match straight_drop 7551 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma rfa_node_7379_position : straight_drop 7550 flat_statements = Some (@Qcons VarOrder.T (@Snode VarOrder.T 7379 rfa_node_7379_expr) rfa_node_7379_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma rfa_node_7379_safe : formal_typed_suffix_safe flat_memories 7379 rfa_node_7379_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma rfa_node_7379_nonreg : has_register 7379 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem rfa_reset_step_7379 inputs path old current result :
 VM.find 1677 old = Some (Gval (Fuint 32) (rfa_reset_word_5 inputs path)) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 VM.find 7379 result = Some (Gval (Fuint 32) (rfa_reset_word_5 inputs path)).
Proof.
 intros Source Step.
 eapply formal_combinational_known_node;
 [exact rfa_node_7379_position|exact rfa_node_7379_safe|exact rfa_node_7379_nonreg| |reflexivity|exact Step].
 cbn [rfa_node_7379_expr eval_hfexpr_validif_policy eval_href_validif_policy]. exact Source.
Qed.
Theorem rfa_reset_history_7379 inputs path history limit :
 (forall t, (t < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history t) false (history t) flat_statements = Some (history (S t))) ->
 forall t, (5 <= t)%coq_nat -> (t <= limit)%coq_nat ->
 VM.find 7379 (history t) = Some (Gval (Fuint 32) (rfa_reset_word_5 inputs path)).
Proof.
 intros Steps t Lower Upper. destruct t as [|t]; [lia|].
 apply (rfa_reset_step_7379 inputs path (history t) (history t) (history (S t))).
 - apply (rfa_reset_history_1677 inputs path history limit Steps t);lia.
 - apply Steps;lia.
Qed.
Definition rfa_node_7380_expr := (@Eref VarOrder.T (@Eid VarOrder.T 7379)).
Definition rfa_node_7380_tail := match straight_drop 7552 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma rfa_node_7380_position : straight_drop 7551 flat_statements = Some (@Qcons VarOrder.T (@Snode VarOrder.T 7380 rfa_node_7380_expr) rfa_node_7380_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma rfa_node_7380_safe : formal_typed_suffix_safe flat_memories 7380 rfa_node_7380_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma rfa_node_7380_nonreg : has_register 7380 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem rfa_reset_step_7380 inputs path old current result :
 VM.find 7379 old = Some (Gval (Fuint 32) (rfa_reset_word_5 inputs path)) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 VM.find 7380 result = Some (Gval (Fuint 32) (rfa_reset_word_5 inputs path)).
Proof.
 intros Source Step.
 eapply formal_combinational_known_node;
 [exact rfa_node_7380_position|exact rfa_node_7380_safe|exact rfa_node_7380_nonreg| |reflexivity|exact Step].
 cbn [rfa_node_7380_expr eval_hfexpr_validif_policy eval_href_validif_policy]. exact Source.
Qed.
Theorem rfa_reset_history_7380 inputs path history limit :
 (forall t, (t < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history t) false (history t) flat_statements = Some (history (S t))) ->
 forall t, (6 <= t)%coq_nat -> (t <= limit)%coq_nat ->
 VM.find 7380 (history t) = Some (Gval (Fuint 32) (rfa_reset_word_5 inputs path)).
Proof.
 intros Steps t Lower Upper. destruct t as [|t]; [lia|].
 apply (rfa_reset_step_7380 inputs path (history t) (history t) (history (S t))).
 - apply (rfa_reset_history_7379 inputs path history limit Steps t);lia.
 - apply Steps;lia.
Qed.
Definition rfa_reset_word_6 inputs path := proj1_sig (formal_symbolic_inputs inputs path (validif_source_address (validif_raw_address nil 8607 0 nil)) nil 32).
Lemma rfa_reset_word_6_size inputs path : size (rfa_reset_word_6 inputs path) = 32%nat.
Proof. exact (proj2_sig (formal_symbolic_inputs inputs path (validif_source_address (validif_raw_address nil 8607 0 nil)) nil 32)). Qed.
Definition rfa_node_8101_expr := (@Evalidif VarOrder.T (@Econst VarOrder.T (Fuint 1) [::false]) (@Econst VarOrder.T (Fuint 32) [::false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false])).
Definition rfa_node_8101_tail := match straight_drop 8608 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma rfa_node_8101_position : straight_drop 8607 flat_statements = Some (@Qcons VarOrder.T (@Snode VarOrder.T 8101 rfa_node_8101_expr) rfa_node_8101_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma rfa_node_8101_safe : formal_typed_suffix_safe flat_memories 8101 rfa_node_8101_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma rfa_node_8101_nonreg : has_register 8101 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem rfa_reset_step_8101 inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 VM.find 8101 result = Some (Gval (Fuint 32) (rfa_reset_word_6 inputs path)).
Proof.
 intros Step.
 eapply formal_combinational_known_node;
 [exact rfa_node_8101_position|exact rfa_node_8101_safe|exact rfa_node_8101_nonreg| |reflexivity|exact Step].
 reflexivity.
Qed.
Theorem rfa_reset_history_8101 inputs path history limit :
 (forall t, (t < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history t) false (history t) flat_statements = Some (history (S t))) ->
 forall t, (1 <= t)%coq_nat -> (t <= limit)%coq_nat ->
 VM.find 8101 (history t) = Some (Gval (Fuint 32) (rfa_reset_word_6 inputs path)).
Proof.
 intros Steps t Lower Upper. destruct t as [|t]; [lia|].
 apply (rfa_reset_step_8101 inputs path (history t) (history t) (history (S t))).
 apply Steps;lia.
Qed.
Definition rfa_node_8102_expr := (@Eref VarOrder.T (@Eid VarOrder.T 8101)).
Definition rfa_node_8102_tail := match straight_drop 8609 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma rfa_node_8102_position : straight_drop 8608 flat_statements = Some (@Qcons VarOrder.T (@Snode VarOrder.T 8102 rfa_node_8102_expr) rfa_node_8102_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma rfa_node_8102_safe : formal_typed_suffix_safe flat_memories 8102 rfa_node_8102_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma rfa_node_8102_nonreg : has_register 8102 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem rfa_reset_step_8102 inputs path old current result :
 VM.find 8101 old = Some (Gval (Fuint 32) (rfa_reset_word_6 inputs path)) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 VM.find 8102 result = Some (Gval (Fuint 32) (rfa_reset_word_6 inputs path)).
Proof.
 intros Source Step.
 eapply formal_combinational_known_node;
 [exact rfa_node_8102_position|exact rfa_node_8102_safe|exact rfa_node_8102_nonreg| |reflexivity|exact Step].
 cbn [rfa_node_8102_expr eval_hfexpr_validif_policy eval_href_validif_policy]. exact Source.
Qed.
Theorem rfa_reset_history_8102 inputs path history limit :
 (forall t, (t < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history t) false (history t) flat_statements = Some (history (S t))) ->
 forall t, (2 <= t)%coq_nat -> (t <= limit)%coq_nat ->
 VM.find 8102 (history t) = Some (Gval (Fuint 32) (rfa_reset_word_6 inputs path)).
Proof.
 intros Steps t Lower Upper. destruct t as [|t]; [lia|].
 apply (rfa_reset_step_8102 inputs path (history t) (history t) (history (S t))).
 - apply (rfa_reset_history_8101 inputs path history limit Steps t);lia.
 - apply Steps;lia.
Qed.
Definition rfa_wire_793_decl := match straight_drop 803 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition rfa_wire_793_tail := match straight_drop 8811 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition rfa_wire_793_mid := take_statements 8007 rfa_wire_793_decl.
Lemma rfa_wire_793_position : straight_drop 802 flat_statements = Some (@Qcons VarOrder.T (@Swire VarOrder.T 793 (Gtyp (Fuint 32))) rfa_wire_793_decl).
Proof. vm_compute. reflexivity. Qed.
Lemma rfa_wire_793_split : rfa_wire_793_decl = statement_append rfa_wire_793_mid (@Qcons VarOrder.T (@Sfcnct VarOrder.T (@Eid VarOrder.T 793) (@Eref VarOrder.T (@Eid VarOrder.T 8102))) rfa_wire_793_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma rfa_wire_793_straight : straight_statements rfa_wire_793_mid.
Proof. vm_compute. exact I. Qed.
Lemma rfa_wire_793_mid_safe : formal_typed_suffix_safe flat_memories 793 rfa_wire_793_mid.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma rfa_wire_793_tail_safe : formal_typed_suffix_safe flat_memories 793 rfa_wire_793_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma rfa_wire_793_nonreg : has_register 793 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem rfa_reset_step_793 inputs path old current result :
 VM.find 8102 old = Some (Gval (Fuint 32) (rfa_reset_word_6 inputs path)) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 VM.find 793 result = Some (Gval (Fuint 32) (rfa_reset_word_6 inputs path)).
Proof.
 intros Source Step.
 apply (declared_connection_value 802 flat_statements rfa_wire_793_decl rfa_wire_793_mid rfa_wire_793_tail 793 8102 32
 (Gval (Fuint 32) (rfa_reset_word_6 inputs path)) (Gval (Fuint 32) (rfa_reset_word_6 inputs path))
 (formal_invalid_policy inputs path) flat_memories old current result rfa_wire_793_position rfa_wire_793_split rfa_wire_793_straight rfa_wire_793_mid_safe rfa_wire_793_tail_safe rfa_wire_793_nonreg (Logic.eq_refl _) Source).
 - assert (Take : take 32 (rfa_reset_word_6 inputs path) = rfa_reset_word_6 inputs path).
   { apply take_oversize. rewrite rfa_reset_word_6_size. reflexivity. }
   cbn [adapt_hvalue_as_type]. rewrite Take. unfold zext_to,zext. rewrite rfa_reset_word_6_size subnn cats0. reflexivity.
 - exact Step.
Qed.
Theorem rfa_reset_history_793 inputs path history limit :
 (forall t, (t < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history t) false (history t) flat_statements = Some (history (S t))) ->
 forall t, (3 <= t)%coq_nat -> (t <= limit)%coq_nat ->
 VM.find 793 (history t) = Some (Gval (Fuint 32) (rfa_reset_word_6 inputs path)).
Proof.
 intros Steps t Lower Upper. destruct t as [|t]; [lia|].
 apply (rfa_reset_step_793 inputs path (history t) (history t) (history (S t))).
 - apply (rfa_reset_history_8102 inputs path history limit Steps t);lia.
 - apply Steps;lia.
Qed.
Definition rfa_node_1091_expr := (@Eref VarOrder.T (@Eid VarOrder.T 793)).
Definition rfa_node_1091_tail := match straight_drop 1101 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma rfa_node_1091_position : straight_drop 1100 flat_statements = Some (@Qcons VarOrder.T (@Snode VarOrder.T 1091 rfa_node_1091_expr) rfa_node_1091_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma rfa_node_1091_safe : formal_typed_suffix_safe flat_memories 1091 rfa_node_1091_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma rfa_node_1091_nonreg : has_register 1091 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem rfa_reset_step_1091 inputs path old current result :
 VM.find 793 old = Some (Gval (Fuint 32) (rfa_reset_word_6 inputs path)) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 VM.find 1091 result = Some (Gval (Fuint 32) (rfa_reset_word_6 inputs path)).
Proof.
 intros Source Step.
 eapply formal_combinational_known_node;
 [exact rfa_node_1091_position|exact rfa_node_1091_safe|exact rfa_node_1091_nonreg| |reflexivity|exact Step].
 cbn [rfa_node_1091_expr eval_hfexpr_validif_policy eval_href_validif_policy]. exact Source.
Qed.
Theorem rfa_reset_history_1091 inputs path history limit :
 (forall t, (t < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history t) false (history t) flat_statements = Some (history (S t))) ->
 forall t, (4 <= t)%coq_nat -> (t <= limit)%coq_nat ->
 VM.find 1091 (history t) = Some (Gval (Fuint 32) (rfa_reset_word_6 inputs path)).
Proof.
 intros Steps t Lower Upper. destruct t as [|t]; [lia|].
 apply (rfa_reset_step_1091 inputs path (history t) (history t) (history (S t))).
 - apply (rfa_reset_history_793 inputs path history limit Steps t);lia.
 - apply Steps;lia.
Qed.
Definition rfa_wire_1488_decl := match straight_drop 1568 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition rfa_wire_1488_tail := match straight_drop 8977 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition rfa_wire_1488_mid := take_statements 7408 rfa_wire_1488_decl.
Lemma rfa_wire_1488_position : straight_drop 1567 flat_statements = Some (@Qcons VarOrder.T (@Swire VarOrder.T 1488 (Gtyp (Fuint 32))) rfa_wire_1488_decl).
Proof. vm_compute. reflexivity. Qed.
Lemma rfa_wire_1488_split : rfa_wire_1488_decl = statement_append rfa_wire_1488_mid (@Qcons VarOrder.T (@Sfcnct VarOrder.T (@Eid VarOrder.T 1488) (@Eref VarOrder.T (@Eid VarOrder.T 8102))) rfa_wire_1488_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma rfa_wire_1488_straight : straight_statements rfa_wire_1488_mid.
Proof. vm_compute. exact I. Qed.
Lemma rfa_wire_1488_mid_safe : formal_typed_suffix_safe flat_memories 1488 rfa_wire_1488_mid.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma rfa_wire_1488_tail_safe : formal_typed_suffix_safe flat_memories 1488 rfa_wire_1488_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma rfa_wire_1488_nonreg : has_register 1488 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem rfa_reset_step_1488 inputs path old current result :
 VM.find 8102 old = Some (Gval (Fuint 32) (rfa_reset_word_6 inputs path)) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 VM.find 1488 result = Some (Gval (Fuint 32) (rfa_reset_word_6 inputs path)).
Proof.
 intros Source Step.
 apply (declared_connection_value 1567 flat_statements rfa_wire_1488_decl rfa_wire_1488_mid rfa_wire_1488_tail 1488 8102 32
 (Gval (Fuint 32) (rfa_reset_word_6 inputs path)) (Gval (Fuint 32) (rfa_reset_word_6 inputs path))
 (formal_invalid_policy inputs path) flat_memories old current result rfa_wire_1488_position rfa_wire_1488_split rfa_wire_1488_straight rfa_wire_1488_mid_safe rfa_wire_1488_tail_safe rfa_wire_1488_nonreg (Logic.eq_refl _) Source).
 - assert (Take : take 32 (rfa_reset_word_6 inputs path) = rfa_reset_word_6 inputs path).
   { apply take_oversize. rewrite rfa_reset_word_6_size. reflexivity. }
   cbn [adapt_hvalue_as_type]. rewrite Take. unfold zext_to,zext. rewrite rfa_reset_word_6_size subnn cats0. reflexivity.
 - exact Step.
Qed.
Theorem rfa_reset_history_1488 inputs path history limit :
 (forall t, (t < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history t) false (history t) flat_statements = Some (history (S t))) ->
 forall t, (3 <= t)%coq_nat -> (t <= limit)%coq_nat ->
 VM.find 1488 (history t) = Some (Gval (Fuint 32) (rfa_reset_word_6 inputs path)).
Proof.
 intros Steps t Lower Upper. destruct t as [|t]; [lia|].
 apply (rfa_reset_step_1488 inputs path (history t) (history t) (history (S t))).
 - apply (rfa_reset_history_8102 inputs path history limit Steps t);lia.
 - apply Steps;lia.
Qed.
Definition rfa_wire_1678_decl := match straight_drop 1758 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition rfa_wire_1678_tail := match straight_drop 8229 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition rfa_wire_1678_mid := take_statements 6470 rfa_wire_1678_decl.
Lemma rfa_wire_1678_position : straight_drop 1757 flat_statements = Some (@Qcons VarOrder.T (@Swire VarOrder.T 1678 (Gtyp (Fuint 32))) rfa_wire_1678_decl).
Proof. vm_compute. reflexivity. Qed.
Lemma rfa_wire_1678_split : rfa_wire_1678_decl = statement_append rfa_wire_1678_mid (@Qcons VarOrder.T (@Sfcnct VarOrder.T (@Eid VarOrder.T 1678) (@Eref VarOrder.T (@Eid VarOrder.T 1488))) rfa_wire_1678_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma rfa_wire_1678_straight : straight_statements rfa_wire_1678_mid.
Proof. vm_compute. exact I. Qed.
Lemma rfa_wire_1678_mid_safe : formal_typed_suffix_safe flat_memories 1678 rfa_wire_1678_mid.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma rfa_wire_1678_tail_safe : formal_typed_suffix_safe flat_memories 1678 rfa_wire_1678_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma rfa_wire_1678_nonreg : has_register 1678 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem rfa_reset_step_1678 inputs path old current result :
 VM.find 1488 old = Some (Gval (Fuint 32) (rfa_reset_word_6 inputs path)) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 VM.find 1678 result = Some (Gval (Fuint 32) (rfa_reset_word_6 inputs path)).
Proof.
 intros Source Step.
 apply (declared_connection_value 1757 flat_statements rfa_wire_1678_decl rfa_wire_1678_mid rfa_wire_1678_tail 1678 1488 32
 (Gval (Fuint 32) (rfa_reset_word_6 inputs path)) (Gval (Fuint 32) (rfa_reset_word_6 inputs path))
 (formal_invalid_policy inputs path) flat_memories old current result rfa_wire_1678_position rfa_wire_1678_split rfa_wire_1678_straight rfa_wire_1678_mid_safe rfa_wire_1678_tail_safe rfa_wire_1678_nonreg (Logic.eq_refl _) Source).
 - assert (Take : take 32 (rfa_reset_word_6 inputs path) = rfa_reset_word_6 inputs path).
   { apply take_oversize. rewrite rfa_reset_word_6_size. reflexivity. }
   cbn [adapt_hvalue_as_type]. rewrite Take. unfold zext_to,zext. rewrite rfa_reset_word_6_size subnn cats0. reflexivity.
 - exact Step.
Qed.
Theorem rfa_reset_history_1678 inputs path history limit :
 (forall t, (t < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history t) false (history t) flat_statements = Some (history (S t))) ->
 forall t, (4 <= t)%coq_nat -> (t <= limit)%coq_nat ->
 VM.find 1678 (history t) = Some (Gval (Fuint 32) (rfa_reset_word_6 inputs path)).
Proof.
 intros Steps t Lower Upper. destruct t as [|t]; [lia|].
 apply (rfa_reset_step_1678 inputs path (history t) (history t) (history (S t))).
 - apply (rfa_reset_history_1488 inputs path history limit Steps t);lia.
 - apply Steps;lia.
Qed.
Definition rfa_node_7381_expr := (@Eref VarOrder.T (@Eid VarOrder.T 1678)).
Definition rfa_node_7381_tail := match straight_drop 7553 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma rfa_node_7381_position : straight_drop 7552 flat_statements = Some (@Qcons VarOrder.T (@Snode VarOrder.T 7381 rfa_node_7381_expr) rfa_node_7381_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma rfa_node_7381_safe : formal_typed_suffix_safe flat_memories 7381 rfa_node_7381_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma rfa_node_7381_nonreg : has_register 7381 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem rfa_reset_step_7381 inputs path old current result :
 VM.find 1678 old = Some (Gval (Fuint 32) (rfa_reset_word_6 inputs path)) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 VM.find 7381 result = Some (Gval (Fuint 32) (rfa_reset_word_6 inputs path)).
Proof.
 intros Source Step.
 eapply formal_combinational_known_node;
 [exact rfa_node_7381_position|exact rfa_node_7381_safe|exact rfa_node_7381_nonreg| |reflexivity|exact Step].
 cbn [rfa_node_7381_expr eval_hfexpr_validif_policy eval_href_validif_policy]. exact Source.
Qed.
Theorem rfa_reset_history_7381 inputs path history limit :
 (forall t, (t < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history t) false (history t) flat_statements = Some (history (S t))) ->
 forall t, (5 <= t)%coq_nat -> (t <= limit)%coq_nat ->
 VM.find 7381 (history t) = Some (Gval (Fuint 32) (rfa_reset_word_6 inputs path)).
Proof.
 intros Steps t Lower Upper. destruct t as [|t]; [lia|].
 apply (rfa_reset_step_7381 inputs path (history t) (history t) (history (S t))).
 - apply (rfa_reset_history_1678 inputs path history limit Steps t);lia.
 - apply Steps;lia.
Qed.
Definition rfa_node_7382_expr := (@Eref VarOrder.T (@Eid VarOrder.T 7381)).
Definition rfa_node_7382_tail := match straight_drop 7554 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma rfa_node_7382_position : straight_drop 7553 flat_statements = Some (@Qcons VarOrder.T (@Snode VarOrder.T 7382 rfa_node_7382_expr) rfa_node_7382_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma rfa_node_7382_safe : formal_typed_suffix_safe flat_memories 7382 rfa_node_7382_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma rfa_node_7382_nonreg : has_register 7382 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem rfa_reset_step_7382 inputs path old current result :
 VM.find 7381 old = Some (Gval (Fuint 32) (rfa_reset_word_6 inputs path)) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 VM.find 7382 result = Some (Gval (Fuint 32) (rfa_reset_word_6 inputs path)).
Proof.
 intros Source Step.
 eapply formal_combinational_known_node;
 [exact rfa_node_7382_position|exact rfa_node_7382_safe|exact rfa_node_7382_nonreg| |reflexivity|exact Step].
 cbn [rfa_node_7382_expr eval_hfexpr_validif_policy eval_href_validif_policy]. exact Source.
Qed.
Theorem rfa_reset_history_7382 inputs path history limit :
 (forall t, (t < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history t) false (history t) flat_statements = Some (history (S t))) ->
 forall t, (6 <= t)%coq_nat -> (t <= limit)%coq_nat ->
 VM.find 7382 (history t) = Some (Gval (Fuint 32) (rfa_reset_word_6 inputs path)).
Proof.
 intros Steps t Lower Upper. destruct t as [|t]; [lia|].
 apply (rfa_reset_step_7382 inputs path (history t) (history t) (history (S t))).
 - apply (rfa_reset_history_7381 inputs path history limit Steps t);lia.
 - apply Steps;lia.
Qed.
Definition rfa_reset_word_7 inputs path := proj1_sig (formal_symbolic_inputs inputs path (validif_source_address (validif_raw_address nil 8609 0 nil)) nil 32).
Lemma rfa_reset_word_7_size inputs path : size (rfa_reset_word_7 inputs path) = 32%nat.
Proof. exact (proj2_sig (formal_symbolic_inputs inputs path (validif_source_address (validif_raw_address nil 8609 0 nil)) nil 32)). Qed.
Definition rfa_node_8103_expr := (@Evalidif VarOrder.T (@Econst VarOrder.T (Fuint 1) [::false]) (@Econst VarOrder.T (Fuint 32) [::false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false])).
Definition rfa_node_8103_tail := match straight_drop 8610 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma rfa_node_8103_position : straight_drop 8609 flat_statements = Some (@Qcons VarOrder.T (@Snode VarOrder.T 8103 rfa_node_8103_expr) rfa_node_8103_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma rfa_node_8103_safe : formal_typed_suffix_safe flat_memories 8103 rfa_node_8103_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma rfa_node_8103_nonreg : has_register 8103 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem rfa_reset_step_8103 inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 VM.find 8103 result = Some (Gval (Fuint 32) (rfa_reset_word_7 inputs path)).
Proof.
 intros Step.
 eapply formal_combinational_known_node;
 [exact rfa_node_8103_position|exact rfa_node_8103_safe|exact rfa_node_8103_nonreg| |reflexivity|exact Step].
 reflexivity.
Qed.
Theorem rfa_reset_history_8103 inputs path history limit :
 (forall t, (t < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history t) false (history t) flat_statements = Some (history (S t))) ->
 forall t, (1 <= t)%coq_nat -> (t <= limit)%coq_nat ->
 VM.find 8103 (history t) = Some (Gval (Fuint 32) (rfa_reset_word_7 inputs path)).
Proof.
 intros Steps t Lower Upper. destruct t as [|t]; [lia|].
 apply (rfa_reset_step_8103 inputs path (history t) (history t) (history (S t))).
 apply Steps;lia.
Qed.
Definition rfa_node_8104_expr := (@Eref VarOrder.T (@Eid VarOrder.T 8103)).
Definition rfa_node_8104_tail := match straight_drop 8611 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma rfa_node_8104_position : straight_drop 8610 flat_statements = Some (@Qcons VarOrder.T (@Snode VarOrder.T 8104 rfa_node_8104_expr) rfa_node_8104_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma rfa_node_8104_safe : formal_typed_suffix_safe flat_memories 8104 rfa_node_8104_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma rfa_node_8104_nonreg : has_register 8104 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem rfa_reset_step_8104 inputs path old current result :
 VM.find 8103 old = Some (Gval (Fuint 32) (rfa_reset_word_7 inputs path)) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 VM.find 8104 result = Some (Gval (Fuint 32) (rfa_reset_word_7 inputs path)).
Proof.
 intros Source Step.
 eapply formal_combinational_known_node;
 [exact rfa_node_8104_position|exact rfa_node_8104_safe|exact rfa_node_8104_nonreg| |reflexivity|exact Step].
 cbn [rfa_node_8104_expr eval_hfexpr_validif_policy eval_href_validif_policy]. exact Source.
Qed.
Theorem rfa_reset_history_8104 inputs path history limit :
 (forall t, (t < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history t) false (history t) flat_statements = Some (history (S t))) ->
 forall t, (2 <= t)%coq_nat -> (t <= limit)%coq_nat ->
 VM.find 8104 (history t) = Some (Gval (Fuint 32) (rfa_reset_word_7 inputs path)).
Proof.
 intros Steps t Lower Upper. destruct t as [|t]; [lia|].
 apply (rfa_reset_step_8104 inputs path (history t) (history t) (history (S t))).
 - apply (rfa_reset_history_8103 inputs path history limit Steps t);lia.
 - apply Steps;lia.
Qed.
Definition rfa_wire_794_decl := match straight_drop 804 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition rfa_wire_794_tail := match straight_drop 8812 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition rfa_wire_794_mid := take_statements 8007 rfa_wire_794_decl.
Lemma rfa_wire_794_position : straight_drop 803 flat_statements = Some (@Qcons VarOrder.T (@Swire VarOrder.T 794 (Gtyp (Fuint 32))) rfa_wire_794_decl).
Proof. vm_compute. reflexivity. Qed.
Lemma rfa_wire_794_split : rfa_wire_794_decl = statement_append rfa_wire_794_mid (@Qcons VarOrder.T (@Sfcnct VarOrder.T (@Eid VarOrder.T 794) (@Eref VarOrder.T (@Eid VarOrder.T 8104))) rfa_wire_794_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma rfa_wire_794_straight : straight_statements rfa_wire_794_mid.
Proof. vm_compute. exact I. Qed.
Lemma rfa_wire_794_mid_safe : formal_typed_suffix_safe flat_memories 794 rfa_wire_794_mid.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma rfa_wire_794_tail_safe : formal_typed_suffix_safe flat_memories 794 rfa_wire_794_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma rfa_wire_794_nonreg : has_register 794 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem rfa_reset_step_794 inputs path old current result :
 VM.find 8104 old = Some (Gval (Fuint 32) (rfa_reset_word_7 inputs path)) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 VM.find 794 result = Some (Gval (Fuint 32) (rfa_reset_word_7 inputs path)).
Proof.
 intros Source Step.
 apply (declared_connection_value 803 flat_statements rfa_wire_794_decl rfa_wire_794_mid rfa_wire_794_tail 794 8104 32
 (Gval (Fuint 32) (rfa_reset_word_7 inputs path)) (Gval (Fuint 32) (rfa_reset_word_7 inputs path))
 (formal_invalid_policy inputs path) flat_memories old current result rfa_wire_794_position rfa_wire_794_split rfa_wire_794_straight rfa_wire_794_mid_safe rfa_wire_794_tail_safe rfa_wire_794_nonreg (Logic.eq_refl _) Source).
 - assert (Take : take 32 (rfa_reset_word_7 inputs path) = rfa_reset_word_7 inputs path).
   { apply take_oversize. rewrite rfa_reset_word_7_size. reflexivity. }
   cbn [adapt_hvalue_as_type]. rewrite Take. unfold zext_to,zext. rewrite rfa_reset_word_7_size subnn cats0. reflexivity.
 - exact Step.
Qed.
Theorem rfa_reset_history_794 inputs path history limit :
 (forall t, (t < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history t) false (history t) flat_statements = Some (history (S t))) ->
 forall t, (3 <= t)%coq_nat -> (t <= limit)%coq_nat ->
 VM.find 794 (history t) = Some (Gval (Fuint 32) (rfa_reset_word_7 inputs path)).
Proof.
 intros Steps t Lower Upper. destruct t as [|t]; [lia|].
 apply (rfa_reset_step_794 inputs path (history t) (history t) (history (S t))).
 - apply (rfa_reset_history_8104 inputs path history limit Steps t);lia.
 - apply Steps;lia.
Qed.
Definition rfa_node_1092_expr := (@Eref VarOrder.T (@Eid VarOrder.T 794)).
Definition rfa_node_1092_tail := match straight_drop 1102 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma rfa_node_1092_position : straight_drop 1101 flat_statements = Some (@Qcons VarOrder.T (@Snode VarOrder.T 1092 rfa_node_1092_expr) rfa_node_1092_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma rfa_node_1092_safe : formal_typed_suffix_safe flat_memories 1092 rfa_node_1092_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma rfa_node_1092_nonreg : has_register 1092 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem rfa_reset_step_1092 inputs path old current result :
 VM.find 794 old = Some (Gval (Fuint 32) (rfa_reset_word_7 inputs path)) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 VM.find 1092 result = Some (Gval (Fuint 32) (rfa_reset_word_7 inputs path)).
Proof.
 intros Source Step.
 eapply formal_combinational_known_node;
 [exact rfa_node_1092_position|exact rfa_node_1092_safe|exact rfa_node_1092_nonreg| |reflexivity|exact Step].
 cbn [rfa_node_1092_expr eval_hfexpr_validif_policy eval_href_validif_policy]. exact Source.
Qed.
Theorem rfa_reset_history_1092 inputs path history limit :
 (forall t, (t < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history t) false (history t) flat_statements = Some (history (S t))) ->
 forall t, (4 <= t)%coq_nat -> (t <= limit)%coq_nat ->
 VM.find 1092 (history t) = Some (Gval (Fuint 32) (rfa_reset_word_7 inputs path)).
Proof.
 intros Steps t Lower Upper. destruct t as [|t]; [lia|].
 apply (rfa_reset_step_1092 inputs path (history t) (history t) (history (S t))).
 - apply (rfa_reset_history_794 inputs path history limit Steps t);lia.
 - apply Steps;lia.
Qed.
Definition rfa_wire_1489_decl := match straight_drop 1569 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition rfa_wire_1489_tail := match straight_drop 8978 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition rfa_wire_1489_mid := take_statements 7408 rfa_wire_1489_decl.
Lemma rfa_wire_1489_position : straight_drop 1568 flat_statements = Some (@Qcons VarOrder.T (@Swire VarOrder.T 1489 (Gtyp (Fuint 32))) rfa_wire_1489_decl).
Proof. vm_compute. reflexivity. Qed.
Lemma rfa_wire_1489_split : rfa_wire_1489_decl = statement_append rfa_wire_1489_mid (@Qcons VarOrder.T (@Sfcnct VarOrder.T (@Eid VarOrder.T 1489) (@Eref VarOrder.T (@Eid VarOrder.T 8104))) rfa_wire_1489_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma rfa_wire_1489_straight : straight_statements rfa_wire_1489_mid.
Proof. vm_compute. exact I. Qed.
Lemma rfa_wire_1489_mid_safe : formal_typed_suffix_safe flat_memories 1489 rfa_wire_1489_mid.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma rfa_wire_1489_tail_safe : formal_typed_suffix_safe flat_memories 1489 rfa_wire_1489_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma rfa_wire_1489_nonreg : has_register 1489 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem rfa_reset_step_1489 inputs path old current result :
 VM.find 8104 old = Some (Gval (Fuint 32) (rfa_reset_word_7 inputs path)) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 VM.find 1489 result = Some (Gval (Fuint 32) (rfa_reset_word_7 inputs path)).
Proof.
 intros Source Step.
 apply (declared_connection_value 1568 flat_statements rfa_wire_1489_decl rfa_wire_1489_mid rfa_wire_1489_tail 1489 8104 32
 (Gval (Fuint 32) (rfa_reset_word_7 inputs path)) (Gval (Fuint 32) (rfa_reset_word_7 inputs path))
 (formal_invalid_policy inputs path) flat_memories old current result rfa_wire_1489_position rfa_wire_1489_split rfa_wire_1489_straight rfa_wire_1489_mid_safe rfa_wire_1489_tail_safe rfa_wire_1489_nonreg (Logic.eq_refl _) Source).
 - assert (Take : take 32 (rfa_reset_word_7 inputs path) = rfa_reset_word_7 inputs path).
   { apply take_oversize. rewrite rfa_reset_word_7_size. reflexivity. }
   cbn [adapt_hvalue_as_type]. rewrite Take. unfold zext_to,zext. rewrite rfa_reset_word_7_size subnn cats0. reflexivity.
 - exact Step.
Qed.
Theorem rfa_reset_history_1489 inputs path history limit :
 (forall t, (t < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history t) false (history t) flat_statements = Some (history (S t))) ->
 forall t, (3 <= t)%coq_nat -> (t <= limit)%coq_nat ->
 VM.find 1489 (history t) = Some (Gval (Fuint 32) (rfa_reset_word_7 inputs path)).
Proof.
 intros Steps t Lower Upper. destruct t as [|t]; [lia|].
 apply (rfa_reset_step_1489 inputs path (history t) (history t) (history (S t))).
 - apply (rfa_reset_history_8104 inputs path history limit Steps t);lia.
 - apply Steps;lia.
Qed.
Definition rfa_wire_1679_decl := match straight_drop 1759 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition rfa_wire_1679_tail := match straight_drop 8230 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition rfa_wire_1679_mid := take_statements 6470 rfa_wire_1679_decl.
Lemma rfa_wire_1679_position : straight_drop 1758 flat_statements = Some (@Qcons VarOrder.T (@Swire VarOrder.T 1679 (Gtyp (Fuint 32))) rfa_wire_1679_decl).
Proof. vm_compute. reflexivity. Qed.
Lemma rfa_wire_1679_split : rfa_wire_1679_decl = statement_append rfa_wire_1679_mid (@Qcons VarOrder.T (@Sfcnct VarOrder.T (@Eid VarOrder.T 1679) (@Eref VarOrder.T (@Eid VarOrder.T 1489))) rfa_wire_1679_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma rfa_wire_1679_straight : straight_statements rfa_wire_1679_mid.
Proof. vm_compute. exact I. Qed.
Lemma rfa_wire_1679_mid_safe : formal_typed_suffix_safe flat_memories 1679 rfa_wire_1679_mid.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma rfa_wire_1679_tail_safe : formal_typed_suffix_safe flat_memories 1679 rfa_wire_1679_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma rfa_wire_1679_nonreg : has_register 1679 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem rfa_reset_step_1679 inputs path old current result :
 VM.find 1489 old = Some (Gval (Fuint 32) (rfa_reset_word_7 inputs path)) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 VM.find 1679 result = Some (Gval (Fuint 32) (rfa_reset_word_7 inputs path)).
Proof.
 intros Source Step.
 apply (declared_connection_value 1758 flat_statements rfa_wire_1679_decl rfa_wire_1679_mid rfa_wire_1679_tail 1679 1489 32
 (Gval (Fuint 32) (rfa_reset_word_7 inputs path)) (Gval (Fuint 32) (rfa_reset_word_7 inputs path))
 (formal_invalid_policy inputs path) flat_memories old current result rfa_wire_1679_position rfa_wire_1679_split rfa_wire_1679_straight rfa_wire_1679_mid_safe rfa_wire_1679_tail_safe rfa_wire_1679_nonreg (Logic.eq_refl _) Source).
 - assert (Take : take 32 (rfa_reset_word_7 inputs path) = rfa_reset_word_7 inputs path).
   { apply take_oversize. rewrite rfa_reset_word_7_size. reflexivity. }
   cbn [adapt_hvalue_as_type]. rewrite Take. unfold zext_to,zext. rewrite rfa_reset_word_7_size subnn cats0. reflexivity.
 - exact Step.
Qed.
Theorem rfa_reset_history_1679 inputs path history limit :
 (forall t, (t < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history t) false (history t) flat_statements = Some (history (S t))) ->
 forall t, (4 <= t)%coq_nat -> (t <= limit)%coq_nat ->
 VM.find 1679 (history t) = Some (Gval (Fuint 32) (rfa_reset_word_7 inputs path)).
Proof.
 intros Steps t Lower Upper. destruct t as [|t]; [lia|].
 apply (rfa_reset_step_1679 inputs path (history t) (history t) (history (S t))).
 - apply (rfa_reset_history_1489 inputs path history limit Steps t);lia.
 - apply Steps;lia.
Qed.
Definition rfa_node_7383_expr := (@Eref VarOrder.T (@Eid VarOrder.T 1679)).
Definition rfa_node_7383_tail := match straight_drop 7555 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma rfa_node_7383_position : straight_drop 7554 flat_statements = Some (@Qcons VarOrder.T (@Snode VarOrder.T 7383 rfa_node_7383_expr) rfa_node_7383_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma rfa_node_7383_safe : formal_typed_suffix_safe flat_memories 7383 rfa_node_7383_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma rfa_node_7383_nonreg : has_register 7383 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem rfa_reset_step_7383 inputs path old current result :
 VM.find 1679 old = Some (Gval (Fuint 32) (rfa_reset_word_7 inputs path)) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 VM.find 7383 result = Some (Gval (Fuint 32) (rfa_reset_word_7 inputs path)).
Proof.
 intros Source Step.
 eapply formal_combinational_known_node;
 [exact rfa_node_7383_position|exact rfa_node_7383_safe|exact rfa_node_7383_nonreg| |reflexivity|exact Step].
 cbn [rfa_node_7383_expr eval_hfexpr_validif_policy eval_href_validif_policy]. exact Source.
Qed.
Theorem rfa_reset_history_7383 inputs path history limit :
 (forall t, (t < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history t) false (history t) flat_statements = Some (history (S t))) ->
 forall t, (5 <= t)%coq_nat -> (t <= limit)%coq_nat ->
 VM.find 7383 (history t) = Some (Gval (Fuint 32) (rfa_reset_word_7 inputs path)).
Proof.
 intros Steps t Lower Upper. destruct t as [|t]; [lia|].
 apply (rfa_reset_step_7383 inputs path (history t) (history t) (history (S t))).
 - apply (rfa_reset_history_1679 inputs path history limit Steps t);lia.
 - apply Steps;lia.
Qed.
Definition rfa_node_7384_expr := (@Eref VarOrder.T (@Eid VarOrder.T 7383)).
Definition rfa_node_7384_tail := match straight_drop 7556 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma rfa_node_7384_position : straight_drop 7555 flat_statements = Some (@Qcons VarOrder.T (@Snode VarOrder.T 7384 rfa_node_7384_expr) rfa_node_7384_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma rfa_node_7384_safe : formal_typed_suffix_safe flat_memories 7384 rfa_node_7384_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma rfa_node_7384_nonreg : has_register 7384 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem rfa_reset_step_7384 inputs path old current result :
 VM.find 7383 old = Some (Gval (Fuint 32) (rfa_reset_word_7 inputs path)) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 VM.find 7384 result = Some (Gval (Fuint 32) (rfa_reset_word_7 inputs path)).
Proof.
 intros Source Step.
 eapply formal_combinational_known_node;
 [exact rfa_node_7384_position|exact rfa_node_7384_safe|exact rfa_node_7384_nonreg| |reflexivity|exact Step].
 cbn [rfa_node_7384_expr eval_hfexpr_validif_policy eval_href_validif_policy]. exact Source.
Qed.
Theorem rfa_reset_history_7384 inputs path history limit :
 (forall t, (t < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history t) false (history t) flat_statements = Some (history (S t))) ->
 forall t, (6 <= t)%coq_nat -> (t <= limit)%coq_nat ->
 VM.find 7384 (history t) = Some (Gval (Fuint 32) (rfa_reset_word_7 inputs path)).
Proof.
 intros Steps t Lower Upper. destruct t as [|t]; [lia|].
 apply (rfa_reset_step_7384 inputs path (history t) (history t) (history (S t))).
 - apply (rfa_reset_history_7383 inputs path history limit Steps t);lia.
 - apply Steps;lia.
Qed.
