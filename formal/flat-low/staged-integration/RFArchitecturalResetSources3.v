Require Import CoreSocModel ComparisonNodes ScalarNodeFrames FormalTypedNodeFrames RegisterInvariants FormalTypedNodeEquation FormalDeclaredConnection FormalStatementSegments RegisterCommitCertificate FormalUIntRegisterCommitSource SelectedUIntMuxIdentity UIntResizeRoundtrip.
From Coq Require Import ZArith List Lia.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From nbits Require Import NBits.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Definition rfa_reset_word_12 inputs path := proj1_sig (formal_symbolic_inputs inputs path (validif_source_address (validif_raw_address nil 8619 0 nil)) nil 32).
Lemma rfa_reset_word_12_size inputs path : size (rfa_reset_word_12 inputs path) = 32%nat.
Proof. exact (proj2_sig (formal_symbolic_inputs inputs path (validif_source_address (validif_raw_address nil 8619 0 nil)) nil 32)). Qed.
Definition rfa_node_8113_expr := (@Evalidif VarOrder.T (@Econst VarOrder.T (Fuint 1) [::false]) (@Econst VarOrder.T (Fuint 32) [::false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false])).
Definition rfa_node_8113_tail := match straight_drop 8620 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma rfa_node_8113_position : straight_drop 8619 flat_statements = Some (@Qcons VarOrder.T (@Snode VarOrder.T 8113 rfa_node_8113_expr) rfa_node_8113_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma rfa_node_8113_safe : formal_typed_suffix_safe flat_memories 8113 rfa_node_8113_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma rfa_node_8113_nonreg : has_register 8113 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem rfa_reset_step_8113 inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 VM.find 8113 result = Some (Gval (Fuint 32) (rfa_reset_word_12 inputs path)).
Proof.
 intros Step.
 eapply formal_combinational_known_node;
 [exact rfa_node_8113_position|exact rfa_node_8113_safe|exact rfa_node_8113_nonreg| |reflexivity|exact Step].
 reflexivity.
Qed.
Theorem rfa_reset_history_8113 inputs path history limit :
 (forall t, (t < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history t) false (history t) flat_statements = Some (history (S t))) ->
 forall t, (1 <= t)%coq_nat -> (t <= limit)%coq_nat ->
 VM.find 8113 (history t) = Some (Gval (Fuint 32) (rfa_reset_word_12 inputs path)).
Proof.
 intros Steps t Lower Upper. destruct t as [|t]; [lia|].
 apply (rfa_reset_step_8113 inputs path (history t) (history t) (history (S t))).
 apply Steps;lia.
Qed.
Definition rfa_node_8114_expr := (@Eref VarOrder.T (@Eid VarOrder.T 8113)).
Definition rfa_node_8114_tail := match straight_drop 8621 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma rfa_node_8114_position : straight_drop 8620 flat_statements = Some (@Qcons VarOrder.T (@Snode VarOrder.T 8114 rfa_node_8114_expr) rfa_node_8114_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma rfa_node_8114_safe : formal_typed_suffix_safe flat_memories 8114 rfa_node_8114_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma rfa_node_8114_nonreg : has_register 8114 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem rfa_reset_step_8114 inputs path old current result :
 VM.find 8113 old = Some (Gval (Fuint 32) (rfa_reset_word_12 inputs path)) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 VM.find 8114 result = Some (Gval (Fuint 32) (rfa_reset_word_12 inputs path)).
Proof.
 intros Source Step.
 eapply formal_combinational_known_node;
 [exact rfa_node_8114_position|exact rfa_node_8114_safe|exact rfa_node_8114_nonreg| |reflexivity|exact Step].
 cbn [rfa_node_8114_expr eval_hfexpr_validif_policy eval_href_validif_policy]. exact Source.
Qed.
Theorem rfa_reset_history_8114 inputs path history limit :
 (forall t, (t < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history t) false (history t) flat_statements = Some (history (S t))) ->
 forall t, (2 <= t)%coq_nat -> (t <= limit)%coq_nat ->
 VM.find 8114 (history t) = Some (Gval (Fuint 32) (rfa_reset_word_12 inputs path)).
Proof.
 intros Steps t Lower Upper. destruct t as [|t]; [lia|].
 apply (rfa_reset_step_8114 inputs path (history t) (history t) (history (S t))).
 - apply (rfa_reset_history_8113 inputs path history limit Steps t);lia.
 - apply Steps;lia.
Qed.
Definition rfa_wire_799_decl := match straight_drop 809 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition rfa_wire_799_tail := match straight_drop 8817 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition rfa_wire_799_mid := take_statements 8007 rfa_wire_799_decl.
Lemma rfa_wire_799_position : straight_drop 808 flat_statements = Some (@Qcons VarOrder.T (@Swire VarOrder.T 799 (Gtyp (Fuint 32))) rfa_wire_799_decl).
Proof. vm_compute. reflexivity. Qed.
Lemma rfa_wire_799_split : rfa_wire_799_decl = statement_append rfa_wire_799_mid (@Qcons VarOrder.T (@Sfcnct VarOrder.T (@Eid VarOrder.T 799) (@Eref VarOrder.T (@Eid VarOrder.T 8114))) rfa_wire_799_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma rfa_wire_799_straight : straight_statements rfa_wire_799_mid.
Proof. vm_compute. exact I. Qed.
Lemma rfa_wire_799_mid_safe : formal_typed_suffix_safe flat_memories 799 rfa_wire_799_mid.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma rfa_wire_799_tail_safe : formal_typed_suffix_safe flat_memories 799 rfa_wire_799_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma rfa_wire_799_nonreg : has_register 799 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem rfa_reset_step_799 inputs path old current result :
 VM.find 8114 old = Some (Gval (Fuint 32) (rfa_reset_word_12 inputs path)) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 VM.find 799 result = Some (Gval (Fuint 32) (rfa_reset_word_12 inputs path)).
Proof.
 intros Source Step.
 apply (declared_connection_value 808 flat_statements rfa_wire_799_decl rfa_wire_799_mid rfa_wire_799_tail 799 8114 32
 (Gval (Fuint 32) (rfa_reset_word_12 inputs path)) (Gval (Fuint 32) (rfa_reset_word_12 inputs path))
 (formal_invalid_policy inputs path) flat_memories old current result rfa_wire_799_position rfa_wire_799_split rfa_wire_799_straight rfa_wire_799_mid_safe rfa_wire_799_tail_safe rfa_wire_799_nonreg (Logic.eq_refl _) Source).
 - assert (Take : take 32 (rfa_reset_word_12 inputs path) = rfa_reset_word_12 inputs path).
   { apply take_oversize. rewrite rfa_reset_word_12_size. reflexivity. }
   cbn [adapt_hvalue_as_type]. rewrite Take. unfold zext_to,zext. rewrite rfa_reset_word_12_size subnn cats0. reflexivity.
 - exact Step.
Qed.
Theorem rfa_reset_history_799 inputs path history limit :
 (forall t, (t < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history t) false (history t) flat_statements = Some (history (S t))) ->
 forall t, (3 <= t)%coq_nat -> (t <= limit)%coq_nat ->
 VM.find 799 (history t) = Some (Gval (Fuint 32) (rfa_reset_word_12 inputs path)).
Proof.
 intros Steps t Lower Upper. destruct t as [|t]; [lia|].
 apply (rfa_reset_step_799 inputs path (history t) (history t) (history (S t))).
 - apply (rfa_reset_history_8114 inputs path history limit Steps t);lia.
 - apply Steps;lia.
Qed.
Definition rfa_node_1097_expr := (@Eref VarOrder.T (@Eid VarOrder.T 799)).
Definition rfa_node_1097_tail := match straight_drop 1107 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma rfa_node_1097_position : straight_drop 1106 flat_statements = Some (@Qcons VarOrder.T (@Snode VarOrder.T 1097 rfa_node_1097_expr) rfa_node_1097_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma rfa_node_1097_safe : formal_typed_suffix_safe flat_memories 1097 rfa_node_1097_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma rfa_node_1097_nonreg : has_register 1097 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem rfa_reset_step_1097 inputs path old current result :
 VM.find 799 old = Some (Gval (Fuint 32) (rfa_reset_word_12 inputs path)) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 VM.find 1097 result = Some (Gval (Fuint 32) (rfa_reset_word_12 inputs path)).
Proof.
 intros Source Step.
 eapply formal_combinational_known_node;
 [exact rfa_node_1097_position|exact rfa_node_1097_safe|exact rfa_node_1097_nonreg| |reflexivity|exact Step].
 cbn [rfa_node_1097_expr eval_hfexpr_validif_policy eval_href_validif_policy]. exact Source.
Qed.
Theorem rfa_reset_history_1097 inputs path history limit :
 (forall t, (t < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history t) false (history t) flat_statements = Some (history (S t))) ->
 forall t, (4 <= t)%coq_nat -> (t <= limit)%coq_nat ->
 VM.find 1097 (history t) = Some (Gval (Fuint 32) (rfa_reset_word_12 inputs path)).
Proof.
 intros Steps t Lower Upper. destruct t as [|t]; [lia|].
 apply (rfa_reset_step_1097 inputs path (history t) (history t) (history (S t))).
 - apply (rfa_reset_history_799 inputs path history limit Steps t);lia.
 - apply Steps;lia.
Qed.
Definition rfa_wire_1494_decl := match straight_drop 1574 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition rfa_wire_1494_tail := match straight_drop 8983 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition rfa_wire_1494_mid := take_statements 7408 rfa_wire_1494_decl.
Lemma rfa_wire_1494_position : straight_drop 1573 flat_statements = Some (@Qcons VarOrder.T (@Swire VarOrder.T 1494 (Gtyp (Fuint 32))) rfa_wire_1494_decl).
Proof. vm_compute. reflexivity. Qed.
Lemma rfa_wire_1494_split : rfa_wire_1494_decl = statement_append rfa_wire_1494_mid (@Qcons VarOrder.T (@Sfcnct VarOrder.T (@Eid VarOrder.T 1494) (@Eref VarOrder.T (@Eid VarOrder.T 8114))) rfa_wire_1494_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma rfa_wire_1494_straight : straight_statements rfa_wire_1494_mid.
Proof. vm_compute. exact I. Qed.
Lemma rfa_wire_1494_mid_safe : formal_typed_suffix_safe flat_memories 1494 rfa_wire_1494_mid.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma rfa_wire_1494_tail_safe : formal_typed_suffix_safe flat_memories 1494 rfa_wire_1494_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma rfa_wire_1494_nonreg : has_register 1494 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem rfa_reset_step_1494 inputs path old current result :
 VM.find 8114 old = Some (Gval (Fuint 32) (rfa_reset_word_12 inputs path)) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 VM.find 1494 result = Some (Gval (Fuint 32) (rfa_reset_word_12 inputs path)).
Proof.
 intros Source Step.
 apply (declared_connection_value 1573 flat_statements rfa_wire_1494_decl rfa_wire_1494_mid rfa_wire_1494_tail 1494 8114 32
 (Gval (Fuint 32) (rfa_reset_word_12 inputs path)) (Gval (Fuint 32) (rfa_reset_word_12 inputs path))
 (formal_invalid_policy inputs path) flat_memories old current result rfa_wire_1494_position rfa_wire_1494_split rfa_wire_1494_straight rfa_wire_1494_mid_safe rfa_wire_1494_tail_safe rfa_wire_1494_nonreg (Logic.eq_refl _) Source).
 - assert (Take : take 32 (rfa_reset_word_12 inputs path) = rfa_reset_word_12 inputs path).
   { apply take_oversize. rewrite rfa_reset_word_12_size. reflexivity. }
   cbn [adapt_hvalue_as_type]. rewrite Take. unfold zext_to,zext. rewrite rfa_reset_word_12_size subnn cats0. reflexivity.
 - exact Step.
Qed.
Theorem rfa_reset_history_1494 inputs path history limit :
 (forall t, (t < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history t) false (history t) flat_statements = Some (history (S t))) ->
 forall t, (3 <= t)%coq_nat -> (t <= limit)%coq_nat ->
 VM.find 1494 (history t) = Some (Gval (Fuint 32) (rfa_reset_word_12 inputs path)).
Proof.
 intros Steps t Lower Upper. destruct t as [|t]; [lia|].
 apply (rfa_reset_step_1494 inputs path (history t) (history t) (history (S t))).
 - apply (rfa_reset_history_8114 inputs path history limit Steps t);lia.
 - apply Steps;lia.
Qed.
Definition rfa_wire_1684_decl := match straight_drop 1764 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition rfa_wire_1684_tail := match straight_drop 8235 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition rfa_wire_1684_mid := take_statements 6470 rfa_wire_1684_decl.
Lemma rfa_wire_1684_position : straight_drop 1763 flat_statements = Some (@Qcons VarOrder.T (@Swire VarOrder.T 1684 (Gtyp (Fuint 32))) rfa_wire_1684_decl).
Proof. vm_compute. reflexivity. Qed.
Lemma rfa_wire_1684_split : rfa_wire_1684_decl = statement_append rfa_wire_1684_mid (@Qcons VarOrder.T (@Sfcnct VarOrder.T (@Eid VarOrder.T 1684) (@Eref VarOrder.T (@Eid VarOrder.T 1494))) rfa_wire_1684_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma rfa_wire_1684_straight : straight_statements rfa_wire_1684_mid.
Proof. vm_compute. exact I. Qed.
Lemma rfa_wire_1684_mid_safe : formal_typed_suffix_safe flat_memories 1684 rfa_wire_1684_mid.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma rfa_wire_1684_tail_safe : formal_typed_suffix_safe flat_memories 1684 rfa_wire_1684_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma rfa_wire_1684_nonreg : has_register 1684 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem rfa_reset_step_1684 inputs path old current result :
 VM.find 1494 old = Some (Gval (Fuint 32) (rfa_reset_word_12 inputs path)) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 VM.find 1684 result = Some (Gval (Fuint 32) (rfa_reset_word_12 inputs path)).
Proof.
 intros Source Step.
 apply (declared_connection_value 1763 flat_statements rfa_wire_1684_decl rfa_wire_1684_mid rfa_wire_1684_tail 1684 1494 32
 (Gval (Fuint 32) (rfa_reset_word_12 inputs path)) (Gval (Fuint 32) (rfa_reset_word_12 inputs path))
 (formal_invalid_policy inputs path) flat_memories old current result rfa_wire_1684_position rfa_wire_1684_split rfa_wire_1684_straight rfa_wire_1684_mid_safe rfa_wire_1684_tail_safe rfa_wire_1684_nonreg (Logic.eq_refl _) Source).
 - assert (Take : take 32 (rfa_reset_word_12 inputs path) = rfa_reset_word_12 inputs path).
   { apply take_oversize. rewrite rfa_reset_word_12_size. reflexivity. }
   cbn [adapt_hvalue_as_type]. rewrite Take. unfold zext_to,zext. rewrite rfa_reset_word_12_size subnn cats0. reflexivity.
 - exact Step.
Qed.
Theorem rfa_reset_history_1684 inputs path history limit :
 (forall t, (t < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history t) false (history t) flat_statements = Some (history (S t))) ->
 forall t, (4 <= t)%coq_nat -> (t <= limit)%coq_nat ->
 VM.find 1684 (history t) = Some (Gval (Fuint 32) (rfa_reset_word_12 inputs path)).
Proof.
 intros Steps t Lower Upper. destruct t as [|t]; [lia|].
 apply (rfa_reset_step_1684 inputs path (history t) (history t) (history (S t))).
 - apply (rfa_reset_history_1494 inputs path history limit Steps t);lia.
 - apply Steps;lia.
Qed.
Definition rfa_node_7393_expr := (@Eref VarOrder.T (@Eid VarOrder.T 1684)).
Definition rfa_node_7393_tail := match straight_drop 7565 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma rfa_node_7393_position : straight_drop 7564 flat_statements = Some (@Qcons VarOrder.T (@Snode VarOrder.T 7393 rfa_node_7393_expr) rfa_node_7393_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma rfa_node_7393_safe : formal_typed_suffix_safe flat_memories 7393 rfa_node_7393_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma rfa_node_7393_nonreg : has_register 7393 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem rfa_reset_step_7393 inputs path old current result :
 VM.find 1684 old = Some (Gval (Fuint 32) (rfa_reset_word_12 inputs path)) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 VM.find 7393 result = Some (Gval (Fuint 32) (rfa_reset_word_12 inputs path)).
Proof.
 intros Source Step.
 eapply formal_combinational_known_node;
 [exact rfa_node_7393_position|exact rfa_node_7393_safe|exact rfa_node_7393_nonreg| |reflexivity|exact Step].
 cbn [rfa_node_7393_expr eval_hfexpr_validif_policy eval_href_validif_policy]. exact Source.
Qed.
Theorem rfa_reset_history_7393 inputs path history limit :
 (forall t, (t < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history t) false (history t) flat_statements = Some (history (S t))) ->
 forall t, (5 <= t)%coq_nat -> (t <= limit)%coq_nat ->
 VM.find 7393 (history t) = Some (Gval (Fuint 32) (rfa_reset_word_12 inputs path)).
Proof.
 intros Steps t Lower Upper. destruct t as [|t]; [lia|].
 apply (rfa_reset_step_7393 inputs path (history t) (history t) (history (S t))).
 - apply (rfa_reset_history_1684 inputs path history limit Steps t);lia.
 - apply Steps;lia.
Qed.
Definition rfa_node_7394_expr := (@Eref VarOrder.T (@Eid VarOrder.T 7393)).
Definition rfa_node_7394_tail := match straight_drop 7566 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma rfa_node_7394_position : straight_drop 7565 flat_statements = Some (@Qcons VarOrder.T (@Snode VarOrder.T 7394 rfa_node_7394_expr) rfa_node_7394_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma rfa_node_7394_safe : formal_typed_suffix_safe flat_memories 7394 rfa_node_7394_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma rfa_node_7394_nonreg : has_register 7394 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem rfa_reset_step_7394 inputs path old current result :
 VM.find 7393 old = Some (Gval (Fuint 32) (rfa_reset_word_12 inputs path)) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 VM.find 7394 result = Some (Gval (Fuint 32) (rfa_reset_word_12 inputs path)).
Proof.
 intros Source Step.
 eapply formal_combinational_known_node;
 [exact rfa_node_7394_position|exact rfa_node_7394_safe|exact rfa_node_7394_nonreg| |reflexivity|exact Step].
 cbn [rfa_node_7394_expr eval_hfexpr_validif_policy eval_href_validif_policy]. exact Source.
Qed.
Theorem rfa_reset_history_7394 inputs path history limit :
 (forall t, (t < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history t) false (history t) flat_statements = Some (history (S t))) ->
 forall t, (6 <= t)%coq_nat -> (t <= limit)%coq_nat ->
 VM.find 7394 (history t) = Some (Gval (Fuint 32) (rfa_reset_word_12 inputs path)).
Proof.
 intros Steps t Lower Upper. destruct t as [|t]; [lia|].
 apply (rfa_reset_step_7394 inputs path (history t) (history t) (history (S t))).
 - apply (rfa_reset_history_7393 inputs path history limit Steps t);lia.
 - apply Steps;lia.
Qed.
Definition rfa_reset_word_13 inputs path := proj1_sig (formal_symbolic_inputs inputs path (validif_source_address (validif_raw_address nil 8621 0 nil)) nil 32).
Lemma rfa_reset_word_13_size inputs path : size (rfa_reset_word_13 inputs path) = 32%nat.
Proof. exact (proj2_sig (formal_symbolic_inputs inputs path (validif_source_address (validif_raw_address nil 8621 0 nil)) nil 32)). Qed.
Definition rfa_node_8115_expr := (@Evalidif VarOrder.T (@Econst VarOrder.T (Fuint 1) [::false]) (@Econst VarOrder.T (Fuint 32) [::false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false])).
Definition rfa_node_8115_tail := match straight_drop 8622 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma rfa_node_8115_position : straight_drop 8621 flat_statements = Some (@Qcons VarOrder.T (@Snode VarOrder.T 8115 rfa_node_8115_expr) rfa_node_8115_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma rfa_node_8115_safe : formal_typed_suffix_safe flat_memories 8115 rfa_node_8115_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma rfa_node_8115_nonreg : has_register 8115 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem rfa_reset_step_8115 inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 VM.find 8115 result = Some (Gval (Fuint 32) (rfa_reset_word_13 inputs path)).
Proof.
 intros Step.
 eapply formal_combinational_known_node;
 [exact rfa_node_8115_position|exact rfa_node_8115_safe|exact rfa_node_8115_nonreg| |reflexivity|exact Step].
 reflexivity.
Qed.
Theorem rfa_reset_history_8115 inputs path history limit :
 (forall t, (t < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history t) false (history t) flat_statements = Some (history (S t))) ->
 forall t, (1 <= t)%coq_nat -> (t <= limit)%coq_nat ->
 VM.find 8115 (history t) = Some (Gval (Fuint 32) (rfa_reset_word_13 inputs path)).
Proof.
 intros Steps t Lower Upper. destruct t as [|t]; [lia|].
 apply (rfa_reset_step_8115 inputs path (history t) (history t) (history (S t))).
 apply Steps;lia.
Qed.
Definition rfa_node_8116_expr := (@Eref VarOrder.T (@Eid VarOrder.T 8115)).
Definition rfa_node_8116_tail := match straight_drop 8623 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma rfa_node_8116_position : straight_drop 8622 flat_statements = Some (@Qcons VarOrder.T (@Snode VarOrder.T 8116 rfa_node_8116_expr) rfa_node_8116_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma rfa_node_8116_safe : formal_typed_suffix_safe flat_memories 8116 rfa_node_8116_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma rfa_node_8116_nonreg : has_register 8116 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem rfa_reset_step_8116 inputs path old current result :
 VM.find 8115 old = Some (Gval (Fuint 32) (rfa_reset_word_13 inputs path)) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 VM.find 8116 result = Some (Gval (Fuint 32) (rfa_reset_word_13 inputs path)).
Proof.
 intros Source Step.
 eapply formal_combinational_known_node;
 [exact rfa_node_8116_position|exact rfa_node_8116_safe|exact rfa_node_8116_nonreg| |reflexivity|exact Step].
 cbn [rfa_node_8116_expr eval_hfexpr_validif_policy eval_href_validif_policy]. exact Source.
Qed.
Theorem rfa_reset_history_8116 inputs path history limit :
 (forall t, (t < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history t) false (history t) flat_statements = Some (history (S t))) ->
 forall t, (2 <= t)%coq_nat -> (t <= limit)%coq_nat ->
 VM.find 8116 (history t) = Some (Gval (Fuint 32) (rfa_reset_word_13 inputs path)).
Proof.
 intros Steps t Lower Upper. destruct t as [|t]; [lia|].
 apply (rfa_reset_step_8116 inputs path (history t) (history t) (history (S t))).
 - apply (rfa_reset_history_8115 inputs path history limit Steps t);lia.
 - apply Steps;lia.
Qed.
Definition rfa_wire_800_decl := match straight_drop 810 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition rfa_wire_800_tail := match straight_drop 8818 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition rfa_wire_800_mid := take_statements 8007 rfa_wire_800_decl.
Lemma rfa_wire_800_position : straight_drop 809 flat_statements = Some (@Qcons VarOrder.T (@Swire VarOrder.T 800 (Gtyp (Fuint 32))) rfa_wire_800_decl).
Proof. vm_compute. reflexivity. Qed.
Lemma rfa_wire_800_split : rfa_wire_800_decl = statement_append rfa_wire_800_mid (@Qcons VarOrder.T (@Sfcnct VarOrder.T (@Eid VarOrder.T 800) (@Eref VarOrder.T (@Eid VarOrder.T 8116))) rfa_wire_800_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma rfa_wire_800_straight : straight_statements rfa_wire_800_mid.
Proof. vm_compute. exact I. Qed.
Lemma rfa_wire_800_mid_safe : formal_typed_suffix_safe flat_memories 800 rfa_wire_800_mid.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma rfa_wire_800_tail_safe : formal_typed_suffix_safe flat_memories 800 rfa_wire_800_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma rfa_wire_800_nonreg : has_register 800 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem rfa_reset_step_800 inputs path old current result :
 VM.find 8116 old = Some (Gval (Fuint 32) (rfa_reset_word_13 inputs path)) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 VM.find 800 result = Some (Gval (Fuint 32) (rfa_reset_word_13 inputs path)).
Proof.
 intros Source Step.
 apply (declared_connection_value 809 flat_statements rfa_wire_800_decl rfa_wire_800_mid rfa_wire_800_tail 800 8116 32
 (Gval (Fuint 32) (rfa_reset_word_13 inputs path)) (Gval (Fuint 32) (rfa_reset_word_13 inputs path))
 (formal_invalid_policy inputs path) flat_memories old current result rfa_wire_800_position rfa_wire_800_split rfa_wire_800_straight rfa_wire_800_mid_safe rfa_wire_800_tail_safe rfa_wire_800_nonreg (Logic.eq_refl _) Source).
 - assert (Take : take 32 (rfa_reset_word_13 inputs path) = rfa_reset_word_13 inputs path).
   { apply take_oversize. rewrite rfa_reset_word_13_size. reflexivity. }
   cbn [adapt_hvalue_as_type]. rewrite Take. unfold zext_to,zext. rewrite rfa_reset_word_13_size subnn cats0. reflexivity.
 - exact Step.
Qed.
Theorem rfa_reset_history_800 inputs path history limit :
 (forall t, (t < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history t) false (history t) flat_statements = Some (history (S t))) ->
 forall t, (3 <= t)%coq_nat -> (t <= limit)%coq_nat ->
 VM.find 800 (history t) = Some (Gval (Fuint 32) (rfa_reset_word_13 inputs path)).
Proof.
 intros Steps t Lower Upper. destruct t as [|t]; [lia|].
 apply (rfa_reset_step_800 inputs path (history t) (history t) (history (S t))).
 - apply (rfa_reset_history_8116 inputs path history limit Steps t);lia.
 - apply Steps;lia.
Qed.
Definition rfa_node_1098_expr := (@Eref VarOrder.T (@Eid VarOrder.T 800)).
Definition rfa_node_1098_tail := match straight_drop 1108 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma rfa_node_1098_position : straight_drop 1107 flat_statements = Some (@Qcons VarOrder.T (@Snode VarOrder.T 1098 rfa_node_1098_expr) rfa_node_1098_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma rfa_node_1098_safe : formal_typed_suffix_safe flat_memories 1098 rfa_node_1098_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma rfa_node_1098_nonreg : has_register 1098 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem rfa_reset_step_1098 inputs path old current result :
 VM.find 800 old = Some (Gval (Fuint 32) (rfa_reset_word_13 inputs path)) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 VM.find 1098 result = Some (Gval (Fuint 32) (rfa_reset_word_13 inputs path)).
Proof.
 intros Source Step.
 eapply formal_combinational_known_node;
 [exact rfa_node_1098_position|exact rfa_node_1098_safe|exact rfa_node_1098_nonreg| |reflexivity|exact Step].
 cbn [rfa_node_1098_expr eval_hfexpr_validif_policy eval_href_validif_policy]. exact Source.
Qed.
Theorem rfa_reset_history_1098 inputs path history limit :
 (forall t, (t < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history t) false (history t) flat_statements = Some (history (S t))) ->
 forall t, (4 <= t)%coq_nat -> (t <= limit)%coq_nat ->
 VM.find 1098 (history t) = Some (Gval (Fuint 32) (rfa_reset_word_13 inputs path)).
Proof.
 intros Steps t Lower Upper. destruct t as [|t]; [lia|].
 apply (rfa_reset_step_1098 inputs path (history t) (history t) (history (S t))).
 - apply (rfa_reset_history_800 inputs path history limit Steps t);lia.
 - apply Steps;lia.
Qed.
Definition rfa_wire_1495_decl := match straight_drop 1575 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition rfa_wire_1495_tail := match straight_drop 8984 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition rfa_wire_1495_mid := take_statements 7408 rfa_wire_1495_decl.
Lemma rfa_wire_1495_position : straight_drop 1574 flat_statements = Some (@Qcons VarOrder.T (@Swire VarOrder.T 1495 (Gtyp (Fuint 32))) rfa_wire_1495_decl).
Proof. vm_compute. reflexivity. Qed.
Lemma rfa_wire_1495_split : rfa_wire_1495_decl = statement_append rfa_wire_1495_mid (@Qcons VarOrder.T (@Sfcnct VarOrder.T (@Eid VarOrder.T 1495) (@Eref VarOrder.T (@Eid VarOrder.T 8116))) rfa_wire_1495_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma rfa_wire_1495_straight : straight_statements rfa_wire_1495_mid.
Proof. vm_compute. exact I. Qed.
Lemma rfa_wire_1495_mid_safe : formal_typed_suffix_safe flat_memories 1495 rfa_wire_1495_mid.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma rfa_wire_1495_tail_safe : formal_typed_suffix_safe flat_memories 1495 rfa_wire_1495_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma rfa_wire_1495_nonreg : has_register 1495 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem rfa_reset_step_1495 inputs path old current result :
 VM.find 8116 old = Some (Gval (Fuint 32) (rfa_reset_word_13 inputs path)) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 VM.find 1495 result = Some (Gval (Fuint 32) (rfa_reset_word_13 inputs path)).
Proof.
 intros Source Step.
 apply (declared_connection_value 1574 flat_statements rfa_wire_1495_decl rfa_wire_1495_mid rfa_wire_1495_tail 1495 8116 32
 (Gval (Fuint 32) (rfa_reset_word_13 inputs path)) (Gval (Fuint 32) (rfa_reset_word_13 inputs path))
 (formal_invalid_policy inputs path) flat_memories old current result rfa_wire_1495_position rfa_wire_1495_split rfa_wire_1495_straight rfa_wire_1495_mid_safe rfa_wire_1495_tail_safe rfa_wire_1495_nonreg (Logic.eq_refl _) Source).
 - assert (Take : take 32 (rfa_reset_word_13 inputs path) = rfa_reset_word_13 inputs path).
   { apply take_oversize. rewrite rfa_reset_word_13_size. reflexivity. }
   cbn [adapt_hvalue_as_type]. rewrite Take. unfold zext_to,zext. rewrite rfa_reset_word_13_size subnn cats0. reflexivity.
 - exact Step.
Qed.
Theorem rfa_reset_history_1495 inputs path history limit :
 (forall t, (t < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history t) false (history t) flat_statements = Some (history (S t))) ->
 forall t, (3 <= t)%coq_nat -> (t <= limit)%coq_nat ->
 VM.find 1495 (history t) = Some (Gval (Fuint 32) (rfa_reset_word_13 inputs path)).
Proof.
 intros Steps t Lower Upper. destruct t as [|t]; [lia|].
 apply (rfa_reset_step_1495 inputs path (history t) (history t) (history (S t))).
 - apply (rfa_reset_history_8116 inputs path history limit Steps t);lia.
 - apply Steps;lia.
Qed.
Definition rfa_wire_1685_decl := match straight_drop 1765 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition rfa_wire_1685_tail := match straight_drop 8236 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition rfa_wire_1685_mid := take_statements 6470 rfa_wire_1685_decl.
Lemma rfa_wire_1685_position : straight_drop 1764 flat_statements = Some (@Qcons VarOrder.T (@Swire VarOrder.T 1685 (Gtyp (Fuint 32))) rfa_wire_1685_decl).
Proof. vm_compute. reflexivity. Qed.
Lemma rfa_wire_1685_split : rfa_wire_1685_decl = statement_append rfa_wire_1685_mid (@Qcons VarOrder.T (@Sfcnct VarOrder.T (@Eid VarOrder.T 1685) (@Eref VarOrder.T (@Eid VarOrder.T 1495))) rfa_wire_1685_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma rfa_wire_1685_straight : straight_statements rfa_wire_1685_mid.
Proof. vm_compute. exact I. Qed.
Lemma rfa_wire_1685_mid_safe : formal_typed_suffix_safe flat_memories 1685 rfa_wire_1685_mid.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma rfa_wire_1685_tail_safe : formal_typed_suffix_safe flat_memories 1685 rfa_wire_1685_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma rfa_wire_1685_nonreg : has_register 1685 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem rfa_reset_step_1685 inputs path old current result :
 VM.find 1495 old = Some (Gval (Fuint 32) (rfa_reset_word_13 inputs path)) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 VM.find 1685 result = Some (Gval (Fuint 32) (rfa_reset_word_13 inputs path)).
Proof.
 intros Source Step.
 apply (declared_connection_value 1764 flat_statements rfa_wire_1685_decl rfa_wire_1685_mid rfa_wire_1685_tail 1685 1495 32
 (Gval (Fuint 32) (rfa_reset_word_13 inputs path)) (Gval (Fuint 32) (rfa_reset_word_13 inputs path))
 (formal_invalid_policy inputs path) flat_memories old current result rfa_wire_1685_position rfa_wire_1685_split rfa_wire_1685_straight rfa_wire_1685_mid_safe rfa_wire_1685_tail_safe rfa_wire_1685_nonreg (Logic.eq_refl _) Source).
 - assert (Take : take 32 (rfa_reset_word_13 inputs path) = rfa_reset_word_13 inputs path).
   { apply take_oversize. rewrite rfa_reset_word_13_size. reflexivity. }
   cbn [adapt_hvalue_as_type]. rewrite Take. unfold zext_to,zext. rewrite rfa_reset_word_13_size subnn cats0. reflexivity.
 - exact Step.
Qed.
Theorem rfa_reset_history_1685 inputs path history limit :
 (forall t, (t < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history t) false (history t) flat_statements = Some (history (S t))) ->
 forall t, (4 <= t)%coq_nat -> (t <= limit)%coq_nat ->
 VM.find 1685 (history t) = Some (Gval (Fuint 32) (rfa_reset_word_13 inputs path)).
Proof.
 intros Steps t Lower Upper. destruct t as [|t]; [lia|].
 apply (rfa_reset_step_1685 inputs path (history t) (history t) (history (S t))).
 - apply (rfa_reset_history_1495 inputs path history limit Steps t);lia.
 - apply Steps;lia.
Qed.
Definition rfa_node_7395_expr := (@Eref VarOrder.T (@Eid VarOrder.T 1685)).
Definition rfa_node_7395_tail := match straight_drop 7567 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma rfa_node_7395_position : straight_drop 7566 flat_statements = Some (@Qcons VarOrder.T (@Snode VarOrder.T 7395 rfa_node_7395_expr) rfa_node_7395_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma rfa_node_7395_safe : formal_typed_suffix_safe flat_memories 7395 rfa_node_7395_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma rfa_node_7395_nonreg : has_register 7395 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem rfa_reset_step_7395 inputs path old current result :
 VM.find 1685 old = Some (Gval (Fuint 32) (rfa_reset_word_13 inputs path)) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 VM.find 7395 result = Some (Gval (Fuint 32) (rfa_reset_word_13 inputs path)).
Proof.
 intros Source Step.
 eapply formal_combinational_known_node;
 [exact rfa_node_7395_position|exact rfa_node_7395_safe|exact rfa_node_7395_nonreg| |reflexivity|exact Step].
 cbn [rfa_node_7395_expr eval_hfexpr_validif_policy eval_href_validif_policy]. exact Source.
Qed.
Theorem rfa_reset_history_7395 inputs path history limit :
 (forall t, (t < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history t) false (history t) flat_statements = Some (history (S t))) ->
 forall t, (5 <= t)%coq_nat -> (t <= limit)%coq_nat ->
 VM.find 7395 (history t) = Some (Gval (Fuint 32) (rfa_reset_word_13 inputs path)).
Proof.
 intros Steps t Lower Upper. destruct t as [|t]; [lia|].
 apply (rfa_reset_step_7395 inputs path (history t) (history t) (history (S t))).
 - apply (rfa_reset_history_1685 inputs path history limit Steps t);lia.
 - apply Steps;lia.
Qed.
Definition rfa_node_7396_expr := (@Eref VarOrder.T (@Eid VarOrder.T 7395)).
Definition rfa_node_7396_tail := match straight_drop 7568 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma rfa_node_7396_position : straight_drop 7567 flat_statements = Some (@Qcons VarOrder.T (@Snode VarOrder.T 7396 rfa_node_7396_expr) rfa_node_7396_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma rfa_node_7396_safe : formal_typed_suffix_safe flat_memories 7396 rfa_node_7396_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma rfa_node_7396_nonreg : has_register 7396 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem rfa_reset_step_7396 inputs path old current result :
 VM.find 7395 old = Some (Gval (Fuint 32) (rfa_reset_word_13 inputs path)) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 VM.find 7396 result = Some (Gval (Fuint 32) (rfa_reset_word_13 inputs path)).
Proof.
 intros Source Step.
 eapply formal_combinational_known_node;
 [exact rfa_node_7396_position|exact rfa_node_7396_safe|exact rfa_node_7396_nonreg| |reflexivity|exact Step].
 cbn [rfa_node_7396_expr eval_hfexpr_validif_policy eval_href_validif_policy]. exact Source.
Qed.
Theorem rfa_reset_history_7396 inputs path history limit :
 (forall t, (t < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history t) false (history t) flat_statements = Some (history (S t))) ->
 forall t, (6 <= t)%coq_nat -> (t <= limit)%coq_nat ->
 VM.find 7396 (history t) = Some (Gval (Fuint 32) (rfa_reset_word_13 inputs path)).
Proof.
 intros Steps t Lower Upper. destruct t as [|t]; [lia|].
 apply (rfa_reset_step_7396 inputs path (history t) (history t) (history (S t))).
 - apply (rfa_reset_history_7395 inputs path history limit Steps t);lia.
 - apply Steps;lia.
Qed.
Definition rfa_reset_word_14 inputs path := proj1_sig (formal_symbolic_inputs inputs path (validif_source_address (validif_raw_address nil 8623 0 nil)) nil 32).
Lemma rfa_reset_word_14_size inputs path : size (rfa_reset_word_14 inputs path) = 32%nat.
Proof. exact (proj2_sig (formal_symbolic_inputs inputs path (validif_source_address (validif_raw_address nil 8623 0 nil)) nil 32)). Qed.
Definition rfa_node_8117_expr := (@Evalidif VarOrder.T (@Econst VarOrder.T (Fuint 1) [::false]) (@Econst VarOrder.T (Fuint 32) [::false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false])).
Definition rfa_node_8117_tail := match straight_drop 8624 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma rfa_node_8117_position : straight_drop 8623 flat_statements = Some (@Qcons VarOrder.T (@Snode VarOrder.T 8117 rfa_node_8117_expr) rfa_node_8117_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma rfa_node_8117_safe : formal_typed_suffix_safe flat_memories 8117 rfa_node_8117_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma rfa_node_8117_nonreg : has_register 8117 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem rfa_reset_step_8117 inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 VM.find 8117 result = Some (Gval (Fuint 32) (rfa_reset_word_14 inputs path)).
Proof.
 intros Step.
 eapply formal_combinational_known_node;
 [exact rfa_node_8117_position|exact rfa_node_8117_safe|exact rfa_node_8117_nonreg| |reflexivity|exact Step].
 reflexivity.
Qed.
Theorem rfa_reset_history_8117 inputs path history limit :
 (forall t, (t < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history t) false (history t) flat_statements = Some (history (S t))) ->
 forall t, (1 <= t)%coq_nat -> (t <= limit)%coq_nat ->
 VM.find 8117 (history t) = Some (Gval (Fuint 32) (rfa_reset_word_14 inputs path)).
Proof.
 intros Steps t Lower Upper. destruct t as [|t]; [lia|].
 apply (rfa_reset_step_8117 inputs path (history t) (history t) (history (S t))).
 apply Steps;lia.
Qed.
Definition rfa_node_8118_expr := (@Eref VarOrder.T (@Eid VarOrder.T 8117)).
Definition rfa_node_8118_tail := match straight_drop 8625 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma rfa_node_8118_position : straight_drop 8624 flat_statements = Some (@Qcons VarOrder.T (@Snode VarOrder.T 8118 rfa_node_8118_expr) rfa_node_8118_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma rfa_node_8118_safe : formal_typed_suffix_safe flat_memories 8118 rfa_node_8118_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma rfa_node_8118_nonreg : has_register 8118 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem rfa_reset_step_8118 inputs path old current result :
 VM.find 8117 old = Some (Gval (Fuint 32) (rfa_reset_word_14 inputs path)) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 VM.find 8118 result = Some (Gval (Fuint 32) (rfa_reset_word_14 inputs path)).
Proof.
 intros Source Step.
 eapply formal_combinational_known_node;
 [exact rfa_node_8118_position|exact rfa_node_8118_safe|exact rfa_node_8118_nonreg| |reflexivity|exact Step].
 cbn [rfa_node_8118_expr eval_hfexpr_validif_policy eval_href_validif_policy]. exact Source.
Qed.
Theorem rfa_reset_history_8118 inputs path history limit :
 (forall t, (t < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history t) false (history t) flat_statements = Some (history (S t))) ->
 forall t, (2 <= t)%coq_nat -> (t <= limit)%coq_nat ->
 VM.find 8118 (history t) = Some (Gval (Fuint 32) (rfa_reset_word_14 inputs path)).
Proof.
 intros Steps t Lower Upper. destruct t as [|t]; [lia|].
 apply (rfa_reset_step_8118 inputs path (history t) (history t) (history (S t))).
 - apply (rfa_reset_history_8117 inputs path history limit Steps t);lia.
 - apply Steps;lia.
Qed.
Definition rfa_wire_801_decl := match straight_drop 811 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition rfa_wire_801_tail := match straight_drop 8819 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition rfa_wire_801_mid := take_statements 8007 rfa_wire_801_decl.
Lemma rfa_wire_801_position : straight_drop 810 flat_statements = Some (@Qcons VarOrder.T (@Swire VarOrder.T 801 (Gtyp (Fuint 32))) rfa_wire_801_decl).
Proof. vm_compute. reflexivity. Qed.
Lemma rfa_wire_801_split : rfa_wire_801_decl = statement_append rfa_wire_801_mid (@Qcons VarOrder.T (@Sfcnct VarOrder.T (@Eid VarOrder.T 801) (@Eref VarOrder.T (@Eid VarOrder.T 8118))) rfa_wire_801_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma rfa_wire_801_straight : straight_statements rfa_wire_801_mid.
Proof. vm_compute. exact I. Qed.
Lemma rfa_wire_801_mid_safe : formal_typed_suffix_safe flat_memories 801 rfa_wire_801_mid.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma rfa_wire_801_tail_safe : formal_typed_suffix_safe flat_memories 801 rfa_wire_801_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma rfa_wire_801_nonreg : has_register 801 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem rfa_reset_step_801 inputs path old current result :
 VM.find 8118 old = Some (Gval (Fuint 32) (rfa_reset_word_14 inputs path)) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 VM.find 801 result = Some (Gval (Fuint 32) (rfa_reset_word_14 inputs path)).
Proof.
 intros Source Step.
 apply (declared_connection_value 810 flat_statements rfa_wire_801_decl rfa_wire_801_mid rfa_wire_801_tail 801 8118 32
 (Gval (Fuint 32) (rfa_reset_word_14 inputs path)) (Gval (Fuint 32) (rfa_reset_word_14 inputs path))
 (formal_invalid_policy inputs path) flat_memories old current result rfa_wire_801_position rfa_wire_801_split rfa_wire_801_straight rfa_wire_801_mid_safe rfa_wire_801_tail_safe rfa_wire_801_nonreg (Logic.eq_refl _) Source).
 - assert (Take : take 32 (rfa_reset_word_14 inputs path) = rfa_reset_word_14 inputs path).
   { apply take_oversize. rewrite rfa_reset_word_14_size. reflexivity. }
   cbn [adapt_hvalue_as_type]. rewrite Take. unfold zext_to,zext. rewrite rfa_reset_word_14_size subnn cats0. reflexivity.
 - exact Step.
Qed.
Theorem rfa_reset_history_801 inputs path history limit :
 (forall t, (t < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history t) false (history t) flat_statements = Some (history (S t))) ->
 forall t, (3 <= t)%coq_nat -> (t <= limit)%coq_nat ->
 VM.find 801 (history t) = Some (Gval (Fuint 32) (rfa_reset_word_14 inputs path)).
Proof.
 intros Steps t Lower Upper. destruct t as [|t]; [lia|].
 apply (rfa_reset_step_801 inputs path (history t) (history t) (history (S t))).
 - apply (rfa_reset_history_8118 inputs path history limit Steps t);lia.
 - apply Steps;lia.
Qed.
Definition rfa_node_1099_expr := (@Eref VarOrder.T (@Eid VarOrder.T 801)).
Definition rfa_node_1099_tail := match straight_drop 1109 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma rfa_node_1099_position : straight_drop 1108 flat_statements = Some (@Qcons VarOrder.T (@Snode VarOrder.T 1099 rfa_node_1099_expr) rfa_node_1099_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma rfa_node_1099_safe : formal_typed_suffix_safe flat_memories 1099 rfa_node_1099_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma rfa_node_1099_nonreg : has_register 1099 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem rfa_reset_step_1099 inputs path old current result :
 VM.find 801 old = Some (Gval (Fuint 32) (rfa_reset_word_14 inputs path)) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 VM.find 1099 result = Some (Gval (Fuint 32) (rfa_reset_word_14 inputs path)).
Proof.
 intros Source Step.
 eapply formal_combinational_known_node;
 [exact rfa_node_1099_position|exact rfa_node_1099_safe|exact rfa_node_1099_nonreg| |reflexivity|exact Step].
 cbn [rfa_node_1099_expr eval_hfexpr_validif_policy eval_href_validif_policy]. exact Source.
Qed.
Theorem rfa_reset_history_1099 inputs path history limit :
 (forall t, (t < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history t) false (history t) flat_statements = Some (history (S t))) ->
 forall t, (4 <= t)%coq_nat -> (t <= limit)%coq_nat ->
 VM.find 1099 (history t) = Some (Gval (Fuint 32) (rfa_reset_word_14 inputs path)).
Proof.
 intros Steps t Lower Upper. destruct t as [|t]; [lia|].
 apply (rfa_reset_step_1099 inputs path (history t) (history t) (history (S t))).
 - apply (rfa_reset_history_801 inputs path history limit Steps t);lia.
 - apply Steps;lia.
Qed.
Definition rfa_wire_1496_decl := match straight_drop 1576 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition rfa_wire_1496_tail := match straight_drop 8985 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition rfa_wire_1496_mid := take_statements 7408 rfa_wire_1496_decl.
Lemma rfa_wire_1496_position : straight_drop 1575 flat_statements = Some (@Qcons VarOrder.T (@Swire VarOrder.T 1496 (Gtyp (Fuint 32))) rfa_wire_1496_decl).
Proof. vm_compute. reflexivity. Qed.
Lemma rfa_wire_1496_split : rfa_wire_1496_decl = statement_append rfa_wire_1496_mid (@Qcons VarOrder.T (@Sfcnct VarOrder.T (@Eid VarOrder.T 1496) (@Eref VarOrder.T (@Eid VarOrder.T 8118))) rfa_wire_1496_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma rfa_wire_1496_straight : straight_statements rfa_wire_1496_mid.
Proof. vm_compute. exact I. Qed.
Lemma rfa_wire_1496_mid_safe : formal_typed_suffix_safe flat_memories 1496 rfa_wire_1496_mid.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma rfa_wire_1496_tail_safe : formal_typed_suffix_safe flat_memories 1496 rfa_wire_1496_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma rfa_wire_1496_nonreg : has_register 1496 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem rfa_reset_step_1496 inputs path old current result :
 VM.find 8118 old = Some (Gval (Fuint 32) (rfa_reset_word_14 inputs path)) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 VM.find 1496 result = Some (Gval (Fuint 32) (rfa_reset_word_14 inputs path)).
Proof.
 intros Source Step.
 apply (declared_connection_value 1575 flat_statements rfa_wire_1496_decl rfa_wire_1496_mid rfa_wire_1496_tail 1496 8118 32
 (Gval (Fuint 32) (rfa_reset_word_14 inputs path)) (Gval (Fuint 32) (rfa_reset_word_14 inputs path))
 (formal_invalid_policy inputs path) flat_memories old current result rfa_wire_1496_position rfa_wire_1496_split rfa_wire_1496_straight rfa_wire_1496_mid_safe rfa_wire_1496_tail_safe rfa_wire_1496_nonreg (Logic.eq_refl _) Source).
 - assert (Take : take 32 (rfa_reset_word_14 inputs path) = rfa_reset_word_14 inputs path).
   { apply take_oversize. rewrite rfa_reset_word_14_size. reflexivity. }
   cbn [adapt_hvalue_as_type]. rewrite Take. unfold zext_to,zext. rewrite rfa_reset_word_14_size subnn cats0. reflexivity.
 - exact Step.
Qed.
Theorem rfa_reset_history_1496 inputs path history limit :
 (forall t, (t < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history t) false (history t) flat_statements = Some (history (S t))) ->
 forall t, (3 <= t)%coq_nat -> (t <= limit)%coq_nat ->
 VM.find 1496 (history t) = Some (Gval (Fuint 32) (rfa_reset_word_14 inputs path)).
Proof.
 intros Steps t Lower Upper. destruct t as [|t]; [lia|].
 apply (rfa_reset_step_1496 inputs path (history t) (history t) (history (S t))).
 - apply (rfa_reset_history_8118 inputs path history limit Steps t);lia.
 - apply Steps;lia.
Qed.
Definition rfa_wire_1686_decl := match straight_drop 1766 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition rfa_wire_1686_tail := match straight_drop 8237 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition rfa_wire_1686_mid := take_statements 6470 rfa_wire_1686_decl.
Lemma rfa_wire_1686_position : straight_drop 1765 flat_statements = Some (@Qcons VarOrder.T (@Swire VarOrder.T 1686 (Gtyp (Fuint 32))) rfa_wire_1686_decl).
Proof. vm_compute. reflexivity. Qed.
Lemma rfa_wire_1686_split : rfa_wire_1686_decl = statement_append rfa_wire_1686_mid (@Qcons VarOrder.T (@Sfcnct VarOrder.T (@Eid VarOrder.T 1686) (@Eref VarOrder.T (@Eid VarOrder.T 1496))) rfa_wire_1686_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma rfa_wire_1686_straight : straight_statements rfa_wire_1686_mid.
Proof. vm_compute. exact I. Qed.
Lemma rfa_wire_1686_mid_safe : formal_typed_suffix_safe flat_memories 1686 rfa_wire_1686_mid.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma rfa_wire_1686_tail_safe : formal_typed_suffix_safe flat_memories 1686 rfa_wire_1686_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma rfa_wire_1686_nonreg : has_register 1686 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem rfa_reset_step_1686 inputs path old current result :
 VM.find 1496 old = Some (Gval (Fuint 32) (rfa_reset_word_14 inputs path)) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 VM.find 1686 result = Some (Gval (Fuint 32) (rfa_reset_word_14 inputs path)).
Proof.
 intros Source Step.
 apply (declared_connection_value 1765 flat_statements rfa_wire_1686_decl rfa_wire_1686_mid rfa_wire_1686_tail 1686 1496 32
 (Gval (Fuint 32) (rfa_reset_word_14 inputs path)) (Gval (Fuint 32) (rfa_reset_word_14 inputs path))
 (formal_invalid_policy inputs path) flat_memories old current result rfa_wire_1686_position rfa_wire_1686_split rfa_wire_1686_straight rfa_wire_1686_mid_safe rfa_wire_1686_tail_safe rfa_wire_1686_nonreg (Logic.eq_refl _) Source).
 - assert (Take : take 32 (rfa_reset_word_14 inputs path) = rfa_reset_word_14 inputs path).
   { apply take_oversize. rewrite rfa_reset_word_14_size. reflexivity. }
   cbn [adapt_hvalue_as_type]. rewrite Take. unfold zext_to,zext. rewrite rfa_reset_word_14_size subnn cats0. reflexivity.
 - exact Step.
Qed.
Theorem rfa_reset_history_1686 inputs path history limit :
 (forall t, (t < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history t) false (history t) flat_statements = Some (history (S t))) ->
 forall t, (4 <= t)%coq_nat -> (t <= limit)%coq_nat ->
 VM.find 1686 (history t) = Some (Gval (Fuint 32) (rfa_reset_word_14 inputs path)).
Proof.
 intros Steps t Lower Upper. destruct t as [|t]; [lia|].
 apply (rfa_reset_step_1686 inputs path (history t) (history t) (history (S t))).
 - apply (rfa_reset_history_1496 inputs path history limit Steps t);lia.
 - apply Steps;lia.
Qed.
Definition rfa_node_7397_expr := (@Eref VarOrder.T (@Eid VarOrder.T 1686)).
Definition rfa_node_7397_tail := match straight_drop 7569 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma rfa_node_7397_position : straight_drop 7568 flat_statements = Some (@Qcons VarOrder.T (@Snode VarOrder.T 7397 rfa_node_7397_expr) rfa_node_7397_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma rfa_node_7397_safe : formal_typed_suffix_safe flat_memories 7397 rfa_node_7397_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma rfa_node_7397_nonreg : has_register 7397 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem rfa_reset_step_7397 inputs path old current result :
 VM.find 1686 old = Some (Gval (Fuint 32) (rfa_reset_word_14 inputs path)) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 VM.find 7397 result = Some (Gval (Fuint 32) (rfa_reset_word_14 inputs path)).
Proof.
 intros Source Step.
 eapply formal_combinational_known_node;
 [exact rfa_node_7397_position|exact rfa_node_7397_safe|exact rfa_node_7397_nonreg| |reflexivity|exact Step].
 cbn [rfa_node_7397_expr eval_hfexpr_validif_policy eval_href_validif_policy]. exact Source.
Qed.
Theorem rfa_reset_history_7397 inputs path history limit :
 (forall t, (t < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history t) false (history t) flat_statements = Some (history (S t))) ->
 forall t, (5 <= t)%coq_nat -> (t <= limit)%coq_nat ->
 VM.find 7397 (history t) = Some (Gval (Fuint 32) (rfa_reset_word_14 inputs path)).
Proof.
 intros Steps t Lower Upper. destruct t as [|t]; [lia|].
 apply (rfa_reset_step_7397 inputs path (history t) (history t) (history (S t))).
 - apply (rfa_reset_history_1686 inputs path history limit Steps t);lia.
 - apply Steps;lia.
Qed.
Definition rfa_node_7398_expr := (@Eref VarOrder.T (@Eid VarOrder.T 7397)).
Definition rfa_node_7398_tail := match straight_drop 7570 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma rfa_node_7398_position : straight_drop 7569 flat_statements = Some (@Qcons VarOrder.T (@Snode VarOrder.T 7398 rfa_node_7398_expr) rfa_node_7398_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma rfa_node_7398_safe : formal_typed_suffix_safe flat_memories 7398 rfa_node_7398_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma rfa_node_7398_nonreg : has_register 7398 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem rfa_reset_step_7398 inputs path old current result :
 VM.find 7397 old = Some (Gval (Fuint 32) (rfa_reset_word_14 inputs path)) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 VM.find 7398 result = Some (Gval (Fuint 32) (rfa_reset_word_14 inputs path)).
Proof.
 intros Source Step.
 eapply formal_combinational_known_node;
 [exact rfa_node_7398_position|exact rfa_node_7398_safe|exact rfa_node_7398_nonreg| |reflexivity|exact Step].
 cbn [rfa_node_7398_expr eval_hfexpr_validif_policy eval_href_validif_policy]. exact Source.
Qed.
Theorem rfa_reset_history_7398 inputs path history limit :
 (forall t, (t < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history t) false (history t) flat_statements = Some (history (S t))) ->
 forall t, (6 <= t)%coq_nat -> (t <= limit)%coq_nat ->
 VM.find 7398 (history t) = Some (Gval (Fuint 32) (rfa_reset_word_14 inputs path)).
Proof.
 intros Steps t Lower Upper. destruct t as [|t]; [lia|].
 apply (rfa_reset_step_7398 inputs path (history t) (history t) (history (S t))).
 - apply (rfa_reset_history_7397 inputs path history limit Steps t);lia.
 - apply Steps;lia.
Qed.
Definition rfa_reset_word_15 inputs path := proj1_sig (formal_symbolic_inputs inputs path (validif_source_address (validif_raw_address nil 8625 0 nil)) nil 32).
Lemma rfa_reset_word_15_size inputs path : size (rfa_reset_word_15 inputs path) = 32%nat.
Proof. exact (proj2_sig (formal_symbolic_inputs inputs path (validif_source_address (validif_raw_address nil 8625 0 nil)) nil 32)). Qed.
Definition rfa_node_8119_expr := (@Evalidif VarOrder.T (@Econst VarOrder.T (Fuint 1) [::false]) (@Econst VarOrder.T (Fuint 32) [::false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false])).
Definition rfa_node_8119_tail := match straight_drop 8626 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma rfa_node_8119_position : straight_drop 8625 flat_statements = Some (@Qcons VarOrder.T (@Snode VarOrder.T 8119 rfa_node_8119_expr) rfa_node_8119_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma rfa_node_8119_safe : formal_typed_suffix_safe flat_memories 8119 rfa_node_8119_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma rfa_node_8119_nonreg : has_register 8119 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem rfa_reset_step_8119 inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 VM.find 8119 result = Some (Gval (Fuint 32) (rfa_reset_word_15 inputs path)).
Proof.
 intros Step.
 eapply formal_combinational_known_node;
 [exact rfa_node_8119_position|exact rfa_node_8119_safe|exact rfa_node_8119_nonreg| |reflexivity|exact Step].
 reflexivity.
Qed.
Theorem rfa_reset_history_8119 inputs path history limit :
 (forall t, (t < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history t) false (history t) flat_statements = Some (history (S t))) ->
 forall t, (1 <= t)%coq_nat -> (t <= limit)%coq_nat ->
 VM.find 8119 (history t) = Some (Gval (Fuint 32) (rfa_reset_word_15 inputs path)).
Proof.
 intros Steps t Lower Upper. destruct t as [|t]; [lia|].
 apply (rfa_reset_step_8119 inputs path (history t) (history t) (history (S t))).
 apply Steps;lia.
Qed.
Definition rfa_node_8120_expr := (@Eref VarOrder.T (@Eid VarOrder.T 8119)).
Definition rfa_node_8120_tail := match straight_drop 8627 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma rfa_node_8120_position : straight_drop 8626 flat_statements = Some (@Qcons VarOrder.T (@Snode VarOrder.T 8120 rfa_node_8120_expr) rfa_node_8120_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma rfa_node_8120_safe : formal_typed_suffix_safe flat_memories 8120 rfa_node_8120_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma rfa_node_8120_nonreg : has_register 8120 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem rfa_reset_step_8120 inputs path old current result :
 VM.find 8119 old = Some (Gval (Fuint 32) (rfa_reset_word_15 inputs path)) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 VM.find 8120 result = Some (Gval (Fuint 32) (rfa_reset_word_15 inputs path)).
Proof.
 intros Source Step.
 eapply formal_combinational_known_node;
 [exact rfa_node_8120_position|exact rfa_node_8120_safe|exact rfa_node_8120_nonreg| |reflexivity|exact Step].
 cbn [rfa_node_8120_expr eval_hfexpr_validif_policy eval_href_validif_policy]. exact Source.
Qed.
Theorem rfa_reset_history_8120 inputs path history limit :
 (forall t, (t < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history t) false (history t) flat_statements = Some (history (S t))) ->
 forall t, (2 <= t)%coq_nat -> (t <= limit)%coq_nat ->
 VM.find 8120 (history t) = Some (Gval (Fuint 32) (rfa_reset_word_15 inputs path)).
Proof.
 intros Steps t Lower Upper. destruct t as [|t]; [lia|].
 apply (rfa_reset_step_8120 inputs path (history t) (history t) (history (S t))).
 - apply (rfa_reset_history_8119 inputs path history limit Steps t);lia.
 - apply Steps;lia.
Qed.
Definition rfa_wire_802_decl := match straight_drop 812 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition rfa_wire_802_tail := match straight_drop 8820 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition rfa_wire_802_mid := take_statements 8007 rfa_wire_802_decl.
Lemma rfa_wire_802_position : straight_drop 811 flat_statements = Some (@Qcons VarOrder.T (@Swire VarOrder.T 802 (Gtyp (Fuint 32))) rfa_wire_802_decl).
Proof. vm_compute. reflexivity. Qed.
Lemma rfa_wire_802_split : rfa_wire_802_decl = statement_append rfa_wire_802_mid (@Qcons VarOrder.T (@Sfcnct VarOrder.T (@Eid VarOrder.T 802) (@Eref VarOrder.T (@Eid VarOrder.T 8120))) rfa_wire_802_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma rfa_wire_802_straight : straight_statements rfa_wire_802_mid.
Proof. vm_compute. exact I. Qed.
Lemma rfa_wire_802_mid_safe : formal_typed_suffix_safe flat_memories 802 rfa_wire_802_mid.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma rfa_wire_802_tail_safe : formal_typed_suffix_safe flat_memories 802 rfa_wire_802_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma rfa_wire_802_nonreg : has_register 802 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem rfa_reset_step_802 inputs path old current result :
 VM.find 8120 old = Some (Gval (Fuint 32) (rfa_reset_word_15 inputs path)) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 VM.find 802 result = Some (Gval (Fuint 32) (rfa_reset_word_15 inputs path)).
Proof.
 intros Source Step.
 apply (declared_connection_value 811 flat_statements rfa_wire_802_decl rfa_wire_802_mid rfa_wire_802_tail 802 8120 32
 (Gval (Fuint 32) (rfa_reset_word_15 inputs path)) (Gval (Fuint 32) (rfa_reset_word_15 inputs path))
 (formal_invalid_policy inputs path) flat_memories old current result rfa_wire_802_position rfa_wire_802_split rfa_wire_802_straight rfa_wire_802_mid_safe rfa_wire_802_tail_safe rfa_wire_802_nonreg (Logic.eq_refl _) Source).
 - assert (Take : take 32 (rfa_reset_word_15 inputs path) = rfa_reset_word_15 inputs path).
   { apply take_oversize. rewrite rfa_reset_word_15_size. reflexivity. }
   cbn [adapt_hvalue_as_type]. rewrite Take. unfold zext_to,zext. rewrite rfa_reset_word_15_size subnn cats0. reflexivity.
 - exact Step.
Qed.
Theorem rfa_reset_history_802 inputs path history limit :
 (forall t, (t < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history t) false (history t) flat_statements = Some (history (S t))) ->
 forall t, (3 <= t)%coq_nat -> (t <= limit)%coq_nat ->
 VM.find 802 (history t) = Some (Gval (Fuint 32) (rfa_reset_word_15 inputs path)).
Proof.
 intros Steps t Lower Upper. destruct t as [|t]; [lia|].
 apply (rfa_reset_step_802 inputs path (history t) (history t) (history (S t))).
 - apply (rfa_reset_history_8120 inputs path history limit Steps t);lia.
 - apply Steps;lia.
Qed.
Definition rfa_node_1100_expr := (@Eref VarOrder.T (@Eid VarOrder.T 802)).
Definition rfa_node_1100_tail := match straight_drop 1110 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma rfa_node_1100_position : straight_drop 1109 flat_statements = Some (@Qcons VarOrder.T (@Snode VarOrder.T 1100 rfa_node_1100_expr) rfa_node_1100_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma rfa_node_1100_safe : formal_typed_suffix_safe flat_memories 1100 rfa_node_1100_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma rfa_node_1100_nonreg : has_register 1100 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem rfa_reset_step_1100 inputs path old current result :
 VM.find 802 old = Some (Gval (Fuint 32) (rfa_reset_word_15 inputs path)) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 VM.find 1100 result = Some (Gval (Fuint 32) (rfa_reset_word_15 inputs path)).
Proof.
 intros Source Step.
 eapply formal_combinational_known_node;
 [exact rfa_node_1100_position|exact rfa_node_1100_safe|exact rfa_node_1100_nonreg| |reflexivity|exact Step].
 cbn [rfa_node_1100_expr eval_hfexpr_validif_policy eval_href_validif_policy]. exact Source.
Qed.
Theorem rfa_reset_history_1100 inputs path history limit :
 (forall t, (t < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history t) false (history t) flat_statements = Some (history (S t))) ->
 forall t, (4 <= t)%coq_nat -> (t <= limit)%coq_nat ->
 VM.find 1100 (history t) = Some (Gval (Fuint 32) (rfa_reset_word_15 inputs path)).
Proof.
 intros Steps t Lower Upper. destruct t as [|t]; [lia|].
 apply (rfa_reset_step_1100 inputs path (history t) (history t) (history (S t))).
 - apply (rfa_reset_history_802 inputs path history limit Steps t);lia.
 - apply Steps;lia.
Qed.
Definition rfa_wire_1497_decl := match straight_drop 1577 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition rfa_wire_1497_tail := match straight_drop 8986 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition rfa_wire_1497_mid := take_statements 7408 rfa_wire_1497_decl.
Lemma rfa_wire_1497_position : straight_drop 1576 flat_statements = Some (@Qcons VarOrder.T (@Swire VarOrder.T 1497 (Gtyp (Fuint 32))) rfa_wire_1497_decl).
Proof. vm_compute. reflexivity. Qed.
Lemma rfa_wire_1497_split : rfa_wire_1497_decl = statement_append rfa_wire_1497_mid (@Qcons VarOrder.T (@Sfcnct VarOrder.T (@Eid VarOrder.T 1497) (@Eref VarOrder.T (@Eid VarOrder.T 8120))) rfa_wire_1497_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma rfa_wire_1497_straight : straight_statements rfa_wire_1497_mid.
Proof. vm_compute. exact I. Qed.
Lemma rfa_wire_1497_mid_safe : formal_typed_suffix_safe flat_memories 1497 rfa_wire_1497_mid.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma rfa_wire_1497_tail_safe : formal_typed_suffix_safe flat_memories 1497 rfa_wire_1497_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma rfa_wire_1497_nonreg : has_register 1497 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem rfa_reset_step_1497 inputs path old current result :
 VM.find 8120 old = Some (Gval (Fuint 32) (rfa_reset_word_15 inputs path)) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 VM.find 1497 result = Some (Gval (Fuint 32) (rfa_reset_word_15 inputs path)).
Proof.
 intros Source Step.
 apply (declared_connection_value 1576 flat_statements rfa_wire_1497_decl rfa_wire_1497_mid rfa_wire_1497_tail 1497 8120 32
 (Gval (Fuint 32) (rfa_reset_word_15 inputs path)) (Gval (Fuint 32) (rfa_reset_word_15 inputs path))
 (formal_invalid_policy inputs path) flat_memories old current result rfa_wire_1497_position rfa_wire_1497_split rfa_wire_1497_straight rfa_wire_1497_mid_safe rfa_wire_1497_tail_safe rfa_wire_1497_nonreg (Logic.eq_refl _) Source).
 - assert (Take : take 32 (rfa_reset_word_15 inputs path) = rfa_reset_word_15 inputs path).
   { apply take_oversize. rewrite rfa_reset_word_15_size. reflexivity. }
   cbn [adapt_hvalue_as_type]. rewrite Take. unfold zext_to,zext. rewrite rfa_reset_word_15_size subnn cats0. reflexivity.
 - exact Step.
Qed.
Theorem rfa_reset_history_1497 inputs path history limit :
 (forall t, (t < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history t) false (history t) flat_statements = Some (history (S t))) ->
 forall t, (3 <= t)%coq_nat -> (t <= limit)%coq_nat ->
 VM.find 1497 (history t) = Some (Gval (Fuint 32) (rfa_reset_word_15 inputs path)).
Proof.
 intros Steps t Lower Upper. destruct t as [|t]; [lia|].
 apply (rfa_reset_step_1497 inputs path (history t) (history t) (history (S t))).
 - apply (rfa_reset_history_8120 inputs path history limit Steps t);lia.
 - apply Steps;lia.
Qed.
Definition rfa_wire_1687_decl := match straight_drop 1767 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition rfa_wire_1687_tail := match straight_drop 8238 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition rfa_wire_1687_mid := take_statements 6470 rfa_wire_1687_decl.
Lemma rfa_wire_1687_position : straight_drop 1766 flat_statements = Some (@Qcons VarOrder.T (@Swire VarOrder.T 1687 (Gtyp (Fuint 32))) rfa_wire_1687_decl).
Proof. vm_compute. reflexivity. Qed.
Lemma rfa_wire_1687_split : rfa_wire_1687_decl = statement_append rfa_wire_1687_mid (@Qcons VarOrder.T (@Sfcnct VarOrder.T (@Eid VarOrder.T 1687) (@Eref VarOrder.T (@Eid VarOrder.T 1497))) rfa_wire_1687_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma rfa_wire_1687_straight : straight_statements rfa_wire_1687_mid.
Proof. vm_compute. exact I. Qed.
Lemma rfa_wire_1687_mid_safe : formal_typed_suffix_safe flat_memories 1687 rfa_wire_1687_mid.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma rfa_wire_1687_tail_safe : formal_typed_suffix_safe flat_memories 1687 rfa_wire_1687_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma rfa_wire_1687_nonreg : has_register 1687 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem rfa_reset_step_1687 inputs path old current result :
 VM.find 1497 old = Some (Gval (Fuint 32) (rfa_reset_word_15 inputs path)) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 VM.find 1687 result = Some (Gval (Fuint 32) (rfa_reset_word_15 inputs path)).
Proof.
 intros Source Step.
 apply (declared_connection_value 1766 flat_statements rfa_wire_1687_decl rfa_wire_1687_mid rfa_wire_1687_tail 1687 1497 32
 (Gval (Fuint 32) (rfa_reset_word_15 inputs path)) (Gval (Fuint 32) (rfa_reset_word_15 inputs path))
 (formal_invalid_policy inputs path) flat_memories old current result rfa_wire_1687_position rfa_wire_1687_split rfa_wire_1687_straight rfa_wire_1687_mid_safe rfa_wire_1687_tail_safe rfa_wire_1687_nonreg (Logic.eq_refl _) Source).
 - assert (Take : take 32 (rfa_reset_word_15 inputs path) = rfa_reset_word_15 inputs path).
   { apply take_oversize. rewrite rfa_reset_word_15_size. reflexivity. }
   cbn [adapt_hvalue_as_type]. rewrite Take. unfold zext_to,zext. rewrite rfa_reset_word_15_size subnn cats0. reflexivity.
 - exact Step.
Qed.
Theorem rfa_reset_history_1687 inputs path history limit :
 (forall t, (t < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history t) false (history t) flat_statements = Some (history (S t))) ->
 forall t, (4 <= t)%coq_nat -> (t <= limit)%coq_nat ->
 VM.find 1687 (history t) = Some (Gval (Fuint 32) (rfa_reset_word_15 inputs path)).
Proof.
 intros Steps t Lower Upper. destruct t as [|t]; [lia|].
 apply (rfa_reset_step_1687 inputs path (history t) (history t) (history (S t))).
 - apply (rfa_reset_history_1497 inputs path history limit Steps t);lia.
 - apply Steps;lia.
Qed.
Definition rfa_node_7399_expr := (@Eref VarOrder.T (@Eid VarOrder.T 1687)).
Definition rfa_node_7399_tail := match straight_drop 7571 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma rfa_node_7399_position : straight_drop 7570 flat_statements = Some (@Qcons VarOrder.T (@Snode VarOrder.T 7399 rfa_node_7399_expr) rfa_node_7399_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma rfa_node_7399_safe : formal_typed_suffix_safe flat_memories 7399 rfa_node_7399_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma rfa_node_7399_nonreg : has_register 7399 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem rfa_reset_step_7399 inputs path old current result :
 VM.find 1687 old = Some (Gval (Fuint 32) (rfa_reset_word_15 inputs path)) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 VM.find 7399 result = Some (Gval (Fuint 32) (rfa_reset_word_15 inputs path)).
Proof.
 intros Source Step.
 eapply formal_combinational_known_node;
 [exact rfa_node_7399_position|exact rfa_node_7399_safe|exact rfa_node_7399_nonreg| |reflexivity|exact Step].
 cbn [rfa_node_7399_expr eval_hfexpr_validif_policy eval_href_validif_policy]. exact Source.
Qed.
Theorem rfa_reset_history_7399 inputs path history limit :
 (forall t, (t < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history t) false (history t) flat_statements = Some (history (S t))) ->
 forall t, (5 <= t)%coq_nat -> (t <= limit)%coq_nat ->
 VM.find 7399 (history t) = Some (Gval (Fuint 32) (rfa_reset_word_15 inputs path)).
Proof.
 intros Steps t Lower Upper. destruct t as [|t]; [lia|].
 apply (rfa_reset_step_7399 inputs path (history t) (history t) (history (S t))).
 - apply (rfa_reset_history_1687 inputs path history limit Steps t);lia.
 - apply Steps;lia.
Qed.
Definition rfa_node_7400_expr := (@Eref VarOrder.T (@Eid VarOrder.T 7399)).
Definition rfa_node_7400_tail := match straight_drop 7572 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma rfa_node_7400_position : straight_drop 7571 flat_statements = Some (@Qcons VarOrder.T (@Snode VarOrder.T 7400 rfa_node_7400_expr) rfa_node_7400_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma rfa_node_7400_safe : formal_typed_suffix_safe flat_memories 7400 rfa_node_7400_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma rfa_node_7400_nonreg : has_register 7400 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem rfa_reset_step_7400 inputs path old current result :
 VM.find 7399 old = Some (Gval (Fuint 32) (rfa_reset_word_15 inputs path)) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 VM.find 7400 result = Some (Gval (Fuint 32) (rfa_reset_word_15 inputs path)).
Proof.
 intros Source Step.
 eapply formal_combinational_known_node;
 [exact rfa_node_7400_position|exact rfa_node_7400_safe|exact rfa_node_7400_nonreg| |reflexivity|exact Step].
 cbn [rfa_node_7400_expr eval_hfexpr_validif_policy eval_href_validif_policy]. exact Source.
Qed.
Theorem rfa_reset_history_7400 inputs path history limit :
 (forall t, (t < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history t) false (history t) flat_statements = Some (history (S t))) ->
 forall t, (6 <= t)%coq_nat -> (t <= limit)%coq_nat ->
 VM.find 7400 (history t) = Some (Gval (Fuint 32) (rfa_reset_word_15 inputs path)).
Proof.
 intros Steps t Lower Upper. destruct t as [|t]; [lia|].
 apply (rfa_reset_step_7400 inputs path (history t) (history t) (history (S t))).
 - apply (rfa_reset_history_7399 inputs path history limit Steps t);lia.
 - apply Steps;lia.
Qed.
