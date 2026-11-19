Require Import CoreSocModel ComparisonNodes ScalarNodeFrames FormalTypedNodeFrames RegisterInvariants FormalTypedNodeEquation FormalDeclaredConnection FormalStatementSegments RegisterCommitCertificate FormalUIntRegisterCommitSource SelectedUIntMuxIdentity UIntResizeRoundtrip.
From Coq Require Import ZArith List Lia.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From nbits Require Import NBits.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Definition rfa_reset_word_0 (inputs : formal_inputs) (path : SVM.key) := zeros 32.
Lemma rfa_reset_word_0_size inputs path : size (rfa_reset_word_0 inputs path) = 32%nat.
Proof. reflexivity. Qed.
Definition rfa_node_8089_expr := (@Econst VarOrder.T (Fuint 32) [::false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false]).
Definition rfa_node_8089_tail := match straight_drop 8596 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma rfa_node_8089_position : straight_drop 8595 flat_statements = Some (@Qcons VarOrder.T (@Snode VarOrder.T 8089 rfa_node_8089_expr) rfa_node_8089_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma rfa_node_8089_safe : formal_typed_suffix_safe flat_memories 8089 rfa_node_8089_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma rfa_node_8089_nonreg : has_register 8089 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem rfa_reset_step_8089 inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 VM.find 8089 result = Some (Gval (Fuint 32) (rfa_reset_word_0 inputs path)).
Proof.
 intros Step.
 eapply formal_combinational_known_node;
 [exact rfa_node_8089_position|exact rfa_node_8089_safe|exact rfa_node_8089_nonreg| |reflexivity|exact Step].
 reflexivity.
Qed.
Theorem rfa_reset_history_8089 inputs path history limit :
 (forall t, (t < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history t) false (history t) flat_statements = Some (history (S t))) ->
 forall t, (1 <= t)%coq_nat -> (t <= limit)%coq_nat ->
 VM.find 8089 (history t) = Some (Gval (Fuint 32) (rfa_reset_word_0 inputs path)).
Proof.
 intros Steps t Lower Upper. destruct t as [|t]; [lia|].
 apply (rfa_reset_step_8089 inputs path (history t) (history t) (history (S t))).
 apply Steps;lia.
Qed.
Definition rfa_node_8090_expr := (@Eref VarOrder.T (@Eid VarOrder.T 8089)).
Definition rfa_node_8090_tail := match straight_drop 8597 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma rfa_node_8090_position : straight_drop 8596 flat_statements = Some (@Qcons VarOrder.T (@Snode VarOrder.T 8090 rfa_node_8090_expr) rfa_node_8090_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma rfa_node_8090_safe : formal_typed_suffix_safe flat_memories 8090 rfa_node_8090_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma rfa_node_8090_nonreg : has_register 8090 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem rfa_reset_step_8090 inputs path old current result :
 VM.find 8089 old = Some (Gval (Fuint 32) (rfa_reset_word_0 inputs path)) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 VM.find 8090 result = Some (Gval (Fuint 32) (rfa_reset_word_0 inputs path)).
Proof.
 intros Source Step.
 eapply formal_combinational_known_node;
 [exact rfa_node_8090_position|exact rfa_node_8090_safe|exact rfa_node_8090_nonreg| |reflexivity|exact Step].
 cbn [rfa_node_8090_expr eval_hfexpr_validif_policy eval_href_validif_policy]. exact Source.
Qed.
Theorem rfa_reset_history_8090 inputs path history limit :
 (forall t, (t < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history t) false (history t) flat_statements = Some (history (S t))) ->
 forall t, (2 <= t)%coq_nat -> (t <= limit)%coq_nat ->
 VM.find 8090 (history t) = Some (Gval (Fuint 32) (rfa_reset_word_0 inputs path)).
Proof.
 intros Steps t Lower Upper. destruct t as [|t]; [lia|].
 apply (rfa_reset_step_8090 inputs path (history t) (history t) (history (S t))).
 - apply (rfa_reset_history_8089 inputs path history limit Steps t);lia.
 - apply Steps;lia.
Qed.
Definition rfa_wire_787_decl := match straight_drop 797 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition rfa_wire_787_tail := match straight_drop 8805 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition rfa_wire_787_mid := take_statements 8007 rfa_wire_787_decl.
Lemma rfa_wire_787_position : straight_drop 796 flat_statements = Some (@Qcons VarOrder.T (@Swire VarOrder.T 787 (Gtyp (Fuint 32))) rfa_wire_787_decl).
Proof. vm_compute. reflexivity. Qed.
Lemma rfa_wire_787_split : rfa_wire_787_decl = statement_append rfa_wire_787_mid (@Qcons VarOrder.T (@Sfcnct VarOrder.T (@Eid VarOrder.T 787) (@Eref VarOrder.T (@Eid VarOrder.T 8090))) rfa_wire_787_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma rfa_wire_787_straight : straight_statements rfa_wire_787_mid.
Proof. vm_compute. exact I. Qed.
Lemma rfa_wire_787_mid_safe : formal_typed_suffix_safe flat_memories 787 rfa_wire_787_mid.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma rfa_wire_787_tail_safe : formal_typed_suffix_safe flat_memories 787 rfa_wire_787_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma rfa_wire_787_nonreg : has_register 787 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem rfa_reset_step_787 inputs path old current result :
 VM.find 8090 old = Some (Gval (Fuint 32) (rfa_reset_word_0 inputs path)) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 VM.find 787 result = Some (Gval (Fuint 32) (rfa_reset_word_0 inputs path)).
Proof.
 intros Source Step.
 apply (declared_connection_value 796 flat_statements rfa_wire_787_decl rfa_wire_787_mid rfa_wire_787_tail 787 8090 32
 (Gval (Fuint 32) (rfa_reset_word_0 inputs path)) (Gval (Fuint 32) (rfa_reset_word_0 inputs path))
 (formal_invalid_policy inputs path) flat_memories old current result rfa_wire_787_position rfa_wire_787_split rfa_wire_787_straight rfa_wire_787_mid_safe rfa_wire_787_tail_safe rfa_wire_787_nonreg (Logic.eq_refl _) Source).
 - assert (Take : take 32 (rfa_reset_word_0 inputs path) = rfa_reset_word_0 inputs path).
   { apply take_oversize. rewrite rfa_reset_word_0_size. reflexivity. }
   cbn [adapt_hvalue_as_type]. rewrite Take. unfold zext_to,zext. rewrite rfa_reset_word_0_size subnn cats0. reflexivity.
 - exact Step.
Qed.
Theorem rfa_reset_history_787 inputs path history limit :
 (forall t, (t < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history t) false (history t) flat_statements = Some (history (S t))) ->
 forall t, (3 <= t)%coq_nat -> (t <= limit)%coq_nat ->
 VM.find 787 (history t) = Some (Gval (Fuint 32) (rfa_reset_word_0 inputs path)).
Proof.
 intros Steps t Lower Upper. destruct t as [|t]; [lia|].
 apply (rfa_reset_step_787 inputs path (history t) (history t) (history (S t))).
 - apply (rfa_reset_history_8090 inputs path history limit Steps t);lia.
 - apply Steps;lia.
Qed.
Definition rfa_node_1085_expr := (@Eref VarOrder.T (@Eid VarOrder.T 787)).
Definition rfa_node_1085_tail := match straight_drop 1095 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma rfa_node_1085_position : straight_drop 1094 flat_statements = Some (@Qcons VarOrder.T (@Snode VarOrder.T 1085 rfa_node_1085_expr) rfa_node_1085_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma rfa_node_1085_safe : formal_typed_suffix_safe flat_memories 1085 rfa_node_1085_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma rfa_node_1085_nonreg : has_register 1085 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem rfa_reset_step_1085 inputs path old current result :
 VM.find 787 old = Some (Gval (Fuint 32) (rfa_reset_word_0 inputs path)) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 VM.find 1085 result = Some (Gval (Fuint 32) (rfa_reset_word_0 inputs path)).
Proof.
 intros Source Step.
 eapply formal_combinational_known_node;
 [exact rfa_node_1085_position|exact rfa_node_1085_safe|exact rfa_node_1085_nonreg| |reflexivity|exact Step].
 cbn [rfa_node_1085_expr eval_hfexpr_validif_policy eval_href_validif_policy]. exact Source.
Qed.
Theorem rfa_reset_history_1085 inputs path history limit :
 (forall t, (t < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history t) false (history t) flat_statements = Some (history (S t))) ->
 forall t, (4 <= t)%coq_nat -> (t <= limit)%coq_nat ->
 VM.find 1085 (history t) = Some (Gval (Fuint 32) (rfa_reset_word_0 inputs path)).
Proof.
 intros Steps t Lower Upper. destruct t as [|t]; [lia|].
 apply (rfa_reset_step_1085 inputs path (history t) (history t) (history (S t))).
 - apply (rfa_reset_history_787 inputs path history limit Steps t);lia.
 - apply Steps;lia.
Qed.
Definition rfa_wire_1482_decl := match straight_drop 1562 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition rfa_wire_1482_tail := match straight_drop 8971 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition rfa_wire_1482_mid := take_statements 7408 rfa_wire_1482_decl.
Lemma rfa_wire_1482_position : straight_drop 1561 flat_statements = Some (@Qcons VarOrder.T (@Swire VarOrder.T 1482 (Gtyp (Fuint 32))) rfa_wire_1482_decl).
Proof. vm_compute. reflexivity. Qed.
Lemma rfa_wire_1482_split : rfa_wire_1482_decl = statement_append rfa_wire_1482_mid (@Qcons VarOrder.T (@Sfcnct VarOrder.T (@Eid VarOrder.T 1482) (@Eref VarOrder.T (@Eid VarOrder.T 8090))) rfa_wire_1482_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma rfa_wire_1482_straight : straight_statements rfa_wire_1482_mid.
Proof. vm_compute. exact I. Qed.
Lemma rfa_wire_1482_mid_safe : formal_typed_suffix_safe flat_memories 1482 rfa_wire_1482_mid.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma rfa_wire_1482_tail_safe : formal_typed_suffix_safe flat_memories 1482 rfa_wire_1482_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma rfa_wire_1482_nonreg : has_register 1482 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem rfa_reset_step_1482 inputs path old current result :
 VM.find 8090 old = Some (Gval (Fuint 32) (rfa_reset_word_0 inputs path)) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 VM.find 1482 result = Some (Gval (Fuint 32) (rfa_reset_word_0 inputs path)).
Proof.
 intros Source Step.
 apply (declared_connection_value 1561 flat_statements rfa_wire_1482_decl rfa_wire_1482_mid rfa_wire_1482_tail 1482 8090 32
 (Gval (Fuint 32) (rfa_reset_word_0 inputs path)) (Gval (Fuint 32) (rfa_reset_word_0 inputs path))
 (formal_invalid_policy inputs path) flat_memories old current result rfa_wire_1482_position rfa_wire_1482_split rfa_wire_1482_straight rfa_wire_1482_mid_safe rfa_wire_1482_tail_safe rfa_wire_1482_nonreg (Logic.eq_refl _) Source).
 - assert (Take : take 32 (rfa_reset_word_0 inputs path) = rfa_reset_word_0 inputs path).
   { apply take_oversize. rewrite rfa_reset_word_0_size. reflexivity. }
   cbn [adapt_hvalue_as_type]. rewrite Take. unfold zext_to,zext. rewrite rfa_reset_word_0_size subnn cats0. reflexivity.
 - exact Step.
Qed.
Theorem rfa_reset_history_1482 inputs path history limit :
 (forall t, (t < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history t) false (history t) flat_statements = Some (history (S t))) ->
 forall t, (3 <= t)%coq_nat -> (t <= limit)%coq_nat ->
 VM.find 1482 (history t) = Some (Gval (Fuint 32) (rfa_reset_word_0 inputs path)).
Proof.
 intros Steps t Lower Upper. destruct t as [|t]; [lia|].
 apply (rfa_reset_step_1482 inputs path (history t) (history t) (history (S t))).
 - apply (rfa_reset_history_8090 inputs path history limit Steps t);lia.
 - apply Steps;lia.
Qed.
Definition rfa_wire_1672_decl := match straight_drop 1752 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition rfa_wire_1672_tail := match straight_drop 8223 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition rfa_wire_1672_mid := take_statements 6470 rfa_wire_1672_decl.
Lemma rfa_wire_1672_position : straight_drop 1751 flat_statements = Some (@Qcons VarOrder.T (@Swire VarOrder.T 1672 (Gtyp (Fuint 32))) rfa_wire_1672_decl).
Proof. vm_compute. reflexivity. Qed.
Lemma rfa_wire_1672_split : rfa_wire_1672_decl = statement_append rfa_wire_1672_mid (@Qcons VarOrder.T (@Sfcnct VarOrder.T (@Eid VarOrder.T 1672) (@Eref VarOrder.T (@Eid VarOrder.T 1482))) rfa_wire_1672_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma rfa_wire_1672_straight : straight_statements rfa_wire_1672_mid.
Proof. vm_compute. exact I. Qed.
Lemma rfa_wire_1672_mid_safe : formal_typed_suffix_safe flat_memories 1672 rfa_wire_1672_mid.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma rfa_wire_1672_tail_safe : formal_typed_suffix_safe flat_memories 1672 rfa_wire_1672_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma rfa_wire_1672_nonreg : has_register 1672 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem rfa_reset_step_1672 inputs path old current result :
 VM.find 1482 old = Some (Gval (Fuint 32) (rfa_reset_word_0 inputs path)) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 VM.find 1672 result = Some (Gval (Fuint 32) (rfa_reset_word_0 inputs path)).
Proof.
 intros Source Step.
 apply (declared_connection_value 1751 flat_statements rfa_wire_1672_decl rfa_wire_1672_mid rfa_wire_1672_tail 1672 1482 32
 (Gval (Fuint 32) (rfa_reset_word_0 inputs path)) (Gval (Fuint 32) (rfa_reset_word_0 inputs path))
 (formal_invalid_policy inputs path) flat_memories old current result rfa_wire_1672_position rfa_wire_1672_split rfa_wire_1672_straight rfa_wire_1672_mid_safe rfa_wire_1672_tail_safe rfa_wire_1672_nonreg (Logic.eq_refl _) Source).
 - assert (Take : take 32 (rfa_reset_word_0 inputs path) = rfa_reset_word_0 inputs path).
   { apply take_oversize. rewrite rfa_reset_word_0_size. reflexivity. }
   cbn [adapt_hvalue_as_type]. rewrite Take. unfold zext_to,zext. rewrite rfa_reset_word_0_size subnn cats0. reflexivity.
 - exact Step.
Qed.
Theorem rfa_reset_history_1672 inputs path history limit :
 (forall t, (t < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history t) false (history t) flat_statements = Some (history (S t))) ->
 forall t, (4 <= t)%coq_nat -> (t <= limit)%coq_nat ->
 VM.find 1672 (history t) = Some (Gval (Fuint 32) (rfa_reset_word_0 inputs path)).
Proof.
 intros Steps t Lower Upper. destruct t as [|t]; [lia|].
 apply (rfa_reset_step_1672 inputs path (history t) (history t) (history (S t))).
 - apply (rfa_reset_history_1482 inputs path history limit Steps t);lia.
 - apply Steps;lia.
Qed.
Definition rfa_node_7369_expr := (@Eref VarOrder.T (@Eid VarOrder.T 1672)).
Definition rfa_node_7369_tail := match straight_drop 7541 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma rfa_node_7369_position : straight_drop 7540 flat_statements = Some (@Qcons VarOrder.T (@Snode VarOrder.T 7369 rfa_node_7369_expr) rfa_node_7369_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma rfa_node_7369_safe : formal_typed_suffix_safe flat_memories 7369 rfa_node_7369_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma rfa_node_7369_nonreg : has_register 7369 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem rfa_reset_step_7369 inputs path old current result :
 VM.find 1672 old = Some (Gval (Fuint 32) (rfa_reset_word_0 inputs path)) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 VM.find 7369 result = Some (Gval (Fuint 32) (rfa_reset_word_0 inputs path)).
Proof.
 intros Source Step.
 eapply formal_combinational_known_node;
 [exact rfa_node_7369_position|exact rfa_node_7369_safe|exact rfa_node_7369_nonreg| |reflexivity|exact Step].
 cbn [rfa_node_7369_expr eval_hfexpr_validif_policy eval_href_validif_policy]. exact Source.
Qed.
Theorem rfa_reset_history_7369 inputs path history limit :
 (forall t, (t < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history t) false (history t) flat_statements = Some (history (S t))) ->
 forall t, (5 <= t)%coq_nat -> (t <= limit)%coq_nat ->
 VM.find 7369 (history t) = Some (Gval (Fuint 32) (rfa_reset_word_0 inputs path)).
Proof.
 intros Steps t Lower Upper. destruct t as [|t]; [lia|].
 apply (rfa_reset_step_7369 inputs path (history t) (history t) (history (S t))).
 - apply (rfa_reset_history_1672 inputs path history limit Steps t);lia.
 - apply Steps;lia.
Qed.
Definition rfa_node_7370_expr := (@Eref VarOrder.T (@Eid VarOrder.T 7369)).
Definition rfa_node_7370_tail := match straight_drop 7542 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma rfa_node_7370_position : straight_drop 7541 flat_statements = Some (@Qcons VarOrder.T (@Snode VarOrder.T 7370 rfa_node_7370_expr) rfa_node_7370_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma rfa_node_7370_safe : formal_typed_suffix_safe flat_memories 7370 rfa_node_7370_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma rfa_node_7370_nonreg : has_register 7370 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem rfa_reset_step_7370 inputs path old current result :
 VM.find 7369 old = Some (Gval (Fuint 32) (rfa_reset_word_0 inputs path)) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 VM.find 7370 result = Some (Gval (Fuint 32) (rfa_reset_word_0 inputs path)).
Proof.
 intros Source Step.
 eapply formal_combinational_known_node;
 [exact rfa_node_7370_position|exact rfa_node_7370_safe|exact rfa_node_7370_nonreg| |reflexivity|exact Step].
 cbn [rfa_node_7370_expr eval_hfexpr_validif_policy eval_href_validif_policy]. exact Source.
Qed.
Theorem rfa_reset_history_7370 inputs path history limit :
 (forall t, (t < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history t) false (history t) flat_statements = Some (history (S t))) ->
 forall t, (6 <= t)%coq_nat -> (t <= limit)%coq_nat ->
 VM.find 7370 (history t) = Some (Gval (Fuint 32) (rfa_reset_word_0 inputs path)).
Proof.
 intros Steps t Lower Upper. destruct t as [|t]; [lia|].
 apply (rfa_reset_step_7370 inputs path (history t) (history t) (history (S t))).
 - apply (rfa_reset_history_7369 inputs path history limit Steps t);lia.
 - apply Steps;lia.
Qed.
Definition rfa_reset_word_1 inputs path := proj1_sig (formal_symbolic_inputs inputs path (validif_source_address (validif_raw_address nil 8597 0 nil)) nil 32).
Lemma rfa_reset_word_1_size inputs path : size (rfa_reset_word_1 inputs path) = 32%nat.
Proof. exact (proj2_sig (formal_symbolic_inputs inputs path (validif_source_address (validif_raw_address nil 8597 0 nil)) nil 32)). Qed.
Definition rfa_node_8091_expr := (@Evalidif VarOrder.T (@Econst VarOrder.T (Fuint 1) [::false]) (@Econst VarOrder.T (Fuint 32) [::false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false])).
Definition rfa_node_8091_tail := match straight_drop 8598 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma rfa_node_8091_position : straight_drop 8597 flat_statements = Some (@Qcons VarOrder.T (@Snode VarOrder.T 8091 rfa_node_8091_expr) rfa_node_8091_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma rfa_node_8091_safe : formal_typed_suffix_safe flat_memories 8091 rfa_node_8091_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma rfa_node_8091_nonreg : has_register 8091 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem rfa_reset_step_8091 inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 VM.find 8091 result = Some (Gval (Fuint 32) (rfa_reset_word_1 inputs path)).
Proof.
 intros Step.
 eapply formal_combinational_known_node;
 [exact rfa_node_8091_position|exact rfa_node_8091_safe|exact rfa_node_8091_nonreg| |reflexivity|exact Step].
 reflexivity.
Qed.
Theorem rfa_reset_history_8091 inputs path history limit :
 (forall t, (t < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history t) false (history t) flat_statements = Some (history (S t))) ->
 forall t, (1 <= t)%coq_nat -> (t <= limit)%coq_nat ->
 VM.find 8091 (history t) = Some (Gval (Fuint 32) (rfa_reset_word_1 inputs path)).
Proof.
 intros Steps t Lower Upper. destruct t as [|t]; [lia|].
 apply (rfa_reset_step_8091 inputs path (history t) (history t) (history (S t))).
 apply Steps;lia.
Qed.
Definition rfa_node_8092_expr := (@Eref VarOrder.T (@Eid VarOrder.T 8091)).
Definition rfa_node_8092_tail := match straight_drop 8599 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma rfa_node_8092_position : straight_drop 8598 flat_statements = Some (@Qcons VarOrder.T (@Snode VarOrder.T 8092 rfa_node_8092_expr) rfa_node_8092_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma rfa_node_8092_safe : formal_typed_suffix_safe flat_memories 8092 rfa_node_8092_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma rfa_node_8092_nonreg : has_register 8092 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem rfa_reset_step_8092 inputs path old current result :
 VM.find 8091 old = Some (Gval (Fuint 32) (rfa_reset_word_1 inputs path)) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 VM.find 8092 result = Some (Gval (Fuint 32) (rfa_reset_word_1 inputs path)).
Proof.
 intros Source Step.
 eapply formal_combinational_known_node;
 [exact rfa_node_8092_position|exact rfa_node_8092_safe|exact rfa_node_8092_nonreg| |reflexivity|exact Step].
 cbn [rfa_node_8092_expr eval_hfexpr_validif_policy eval_href_validif_policy]. exact Source.
Qed.
Theorem rfa_reset_history_8092 inputs path history limit :
 (forall t, (t < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history t) false (history t) flat_statements = Some (history (S t))) ->
 forall t, (2 <= t)%coq_nat -> (t <= limit)%coq_nat ->
 VM.find 8092 (history t) = Some (Gval (Fuint 32) (rfa_reset_word_1 inputs path)).
Proof.
 intros Steps t Lower Upper. destruct t as [|t]; [lia|].
 apply (rfa_reset_step_8092 inputs path (history t) (history t) (history (S t))).
 - apply (rfa_reset_history_8091 inputs path history limit Steps t);lia.
 - apply Steps;lia.
Qed.
Definition rfa_wire_788_decl := match straight_drop 798 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition rfa_wire_788_tail := match straight_drop 8806 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition rfa_wire_788_mid := take_statements 8007 rfa_wire_788_decl.
Lemma rfa_wire_788_position : straight_drop 797 flat_statements = Some (@Qcons VarOrder.T (@Swire VarOrder.T 788 (Gtyp (Fuint 32))) rfa_wire_788_decl).
Proof. vm_compute. reflexivity. Qed.
Lemma rfa_wire_788_split : rfa_wire_788_decl = statement_append rfa_wire_788_mid (@Qcons VarOrder.T (@Sfcnct VarOrder.T (@Eid VarOrder.T 788) (@Eref VarOrder.T (@Eid VarOrder.T 8092))) rfa_wire_788_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma rfa_wire_788_straight : straight_statements rfa_wire_788_mid.
Proof. vm_compute. exact I. Qed.
Lemma rfa_wire_788_mid_safe : formal_typed_suffix_safe flat_memories 788 rfa_wire_788_mid.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma rfa_wire_788_tail_safe : formal_typed_suffix_safe flat_memories 788 rfa_wire_788_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma rfa_wire_788_nonreg : has_register 788 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem rfa_reset_step_788 inputs path old current result :
 VM.find 8092 old = Some (Gval (Fuint 32) (rfa_reset_word_1 inputs path)) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 VM.find 788 result = Some (Gval (Fuint 32) (rfa_reset_word_1 inputs path)).
Proof.
 intros Source Step.
 apply (declared_connection_value 797 flat_statements rfa_wire_788_decl rfa_wire_788_mid rfa_wire_788_tail 788 8092 32
 (Gval (Fuint 32) (rfa_reset_word_1 inputs path)) (Gval (Fuint 32) (rfa_reset_word_1 inputs path))
 (formal_invalid_policy inputs path) flat_memories old current result rfa_wire_788_position rfa_wire_788_split rfa_wire_788_straight rfa_wire_788_mid_safe rfa_wire_788_tail_safe rfa_wire_788_nonreg (Logic.eq_refl _) Source).
 - assert (Take : take 32 (rfa_reset_word_1 inputs path) = rfa_reset_word_1 inputs path).
   { apply take_oversize. rewrite rfa_reset_word_1_size. reflexivity. }
   cbn [adapt_hvalue_as_type]. rewrite Take. unfold zext_to,zext. rewrite rfa_reset_word_1_size subnn cats0. reflexivity.
 - exact Step.
Qed.
Theorem rfa_reset_history_788 inputs path history limit :
 (forall t, (t < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history t) false (history t) flat_statements = Some (history (S t))) ->
 forall t, (3 <= t)%coq_nat -> (t <= limit)%coq_nat ->
 VM.find 788 (history t) = Some (Gval (Fuint 32) (rfa_reset_word_1 inputs path)).
Proof.
 intros Steps t Lower Upper. destruct t as [|t]; [lia|].
 apply (rfa_reset_step_788 inputs path (history t) (history t) (history (S t))).
 - apply (rfa_reset_history_8092 inputs path history limit Steps t);lia.
 - apply Steps;lia.
Qed.
Definition rfa_node_1086_expr := (@Eref VarOrder.T (@Eid VarOrder.T 788)).
Definition rfa_node_1086_tail := match straight_drop 1096 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma rfa_node_1086_position : straight_drop 1095 flat_statements = Some (@Qcons VarOrder.T (@Snode VarOrder.T 1086 rfa_node_1086_expr) rfa_node_1086_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma rfa_node_1086_safe : formal_typed_suffix_safe flat_memories 1086 rfa_node_1086_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma rfa_node_1086_nonreg : has_register 1086 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem rfa_reset_step_1086 inputs path old current result :
 VM.find 788 old = Some (Gval (Fuint 32) (rfa_reset_word_1 inputs path)) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 VM.find 1086 result = Some (Gval (Fuint 32) (rfa_reset_word_1 inputs path)).
Proof.
 intros Source Step.
 eapply formal_combinational_known_node;
 [exact rfa_node_1086_position|exact rfa_node_1086_safe|exact rfa_node_1086_nonreg| |reflexivity|exact Step].
 cbn [rfa_node_1086_expr eval_hfexpr_validif_policy eval_href_validif_policy]. exact Source.
Qed.
Theorem rfa_reset_history_1086 inputs path history limit :
 (forall t, (t < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history t) false (history t) flat_statements = Some (history (S t))) ->
 forall t, (4 <= t)%coq_nat -> (t <= limit)%coq_nat ->
 VM.find 1086 (history t) = Some (Gval (Fuint 32) (rfa_reset_word_1 inputs path)).
Proof.
 intros Steps t Lower Upper. destruct t as [|t]; [lia|].
 apply (rfa_reset_step_1086 inputs path (history t) (history t) (history (S t))).
 - apply (rfa_reset_history_788 inputs path history limit Steps t);lia.
 - apply Steps;lia.
Qed.
Definition rfa_wire_1483_decl := match straight_drop 1563 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition rfa_wire_1483_tail := match straight_drop 8972 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition rfa_wire_1483_mid := take_statements 7408 rfa_wire_1483_decl.
Lemma rfa_wire_1483_position : straight_drop 1562 flat_statements = Some (@Qcons VarOrder.T (@Swire VarOrder.T 1483 (Gtyp (Fuint 32))) rfa_wire_1483_decl).
Proof. vm_compute. reflexivity. Qed.
Lemma rfa_wire_1483_split : rfa_wire_1483_decl = statement_append rfa_wire_1483_mid (@Qcons VarOrder.T (@Sfcnct VarOrder.T (@Eid VarOrder.T 1483) (@Eref VarOrder.T (@Eid VarOrder.T 8092))) rfa_wire_1483_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma rfa_wire_1483_straight : straight_statements rfa_wire_1483_mid.
Proof. vm_compute. exact I. Qed.
Lemma rfa_wire_1483_mid_safe : formal_typed_suffix_safe flat_memories 1483 rfa_wire_1483_mid.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma rfa_wire_1483_tail_safe : formal_typed_suffix_safe flat_memories 1483 rfa_wire_1483_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma rfa_wire_1483_nonreg : has_register 1483 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem rfa_reset_step_1483 inputs path old current result :
 VM.find 8092 old = Some (Gval (Fuint 32) (rfa_reset_word_1 inputs path)) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 VM.find 1483 result = Some (Gval (Fuint 32) (rfa_reset_word_1 inputs path)).
Proof.
 intros Source Step.
 apply (declared_connection_value 1562 flat_statements rfa_wire_1483_decl rfa_wire_1483_mid rfa_wire_1483_tail 1483 8092 32
 (Gval (Fuint 32) (rfa_reset_word_1 inputs path)) (Gval (Fuint 32) (rfa_reset_word_1 inputs path))
 (formal_invalid_policy inputs path) flat_memories old current result rfa_wire_1483_position rfa_wire_1483_split rfa_wire_1483_straight rfa_wire_1483_mid_safe rfa_wire_1483_tail_safe rfa_wire_1483_nonreg (Logic.eq_refl _) Source).
 - assert (Take : take 32 (rfa_reset_word_1 inputs path) = rfa_reset_word_1 inputs path).
   { apply take_oversize. rewrite rfa_reset_word_1_size. reflexivity. }
   cbn [adapt_hvalue_as_type]. rewrite Take. unfold zext_to,zext. rewrite rfa_reset_word_1_size subnn cats0. reflexivity.
 - exact Step.
Qed.
Theorem rfa_reset_history_1483 inputs path history limit :
 (forall t, (t < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history t) false (history t) flat_statements = Some (history (S t))) ->
 forall t, (3 <= t)%coq_nat -> (t <= limit)%coq_nat ->
 VM.find 1483 (history t) = Some (Gval (Fuint 32) (rfa_reset_word_1 inputs path)).
Proof.
 intros Steps t Lower Upper. destruct t as [|t]; [lia|].
 apply (rfa_reset_step_1483 inputs path (history t) (history t) (history (S t))).
 - apply (rfa_reset_history_8092 inputs path history limit Steps t);lia.
 - apply Steps;lia.
Qed.
Definition rfa_wire_1673_decl := match straight_drop 1753 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition rfa_wire_1673_tail := match straight_drop 8224 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition rfa_wire_1673_mid := take_statements 6470 rfa_wire_1673_decl.
Lemma rfa_wire_1673_position : straight_drop 1752 flat_statements = Some (@Qcons VarOrder.T (@Swire VarOrder.T 1673 (Gtyp (Fuint 32))) rfa_wire_1673_decl).
Proof. vm_compute. reflexivity. Qed.
Lemma rfa_wire_1673_split : rfa_wire_1673_decl = statement_append rfa_wire_1673_mid (@Qcons VarOrder.T (@Sfcnct VarOrder.T (@Eid VarOrder.T 1673) (@Eref VarOrder.T (@Eid VarOrder.T 1483))) rfa_wire_1673_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma rfa_wire_1673_straight : straight_statements rfa_wire_1673_mid.
Proof. vm_compute. exact I. Qed.
Lemma rfa_wire_1673_mid_safe : formal_typed_suffix_safe flat_memories 1673 rfa_wire_1673_mid.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma rfa_wire_1673_tail_safe : formal_typed_suffix_safe flat_memories 1673 rfa_wire_1673_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma rfa_wire_1673_nonreg : has_register 1673 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem rfa_reset_step_1673 inputs path old current result :
 VM.find 1483 old = Some (Gval (Fuint 32) (rfa_reset_word_1 inputs path)) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 VM.find 1673 result = Some (Gval (Fuint 32) (rfa_reset_word_1 inputs path)).
Proof.
 intros Source Step.
 apply (declared_connection_value 1752 flat_statements rfa_wire_1673_decl rfa_wire_1673_mid rfa_wire_1673_tail 1673 1483 32
 (Gval (Fuint 32) (rfa_reset_word_1 inputs path)) (Gval (Fuint 32) (rfa_reset_word_1 inputs path))
 (formal_invalid_policy inputs path) flat_memories old current result rfa_wire_1673_position rfa_wire_1673_split rfa_wire_1673_straight rfa_wire_1673_mid_safe rfa_wire_1673_tail_safe rfa_wire_1673_nonreg (Logic.eq_refl _) Source).
 - assert (Take : take 32 (rfa_reset_word_1 inputs path) = rfa_reset_word_1 inputs path).
   { apply take_oversize. rewrite rfa_reset_word_1_size. reflexivity. }
   cbn [adapt_hvalue_as_type]. rewrite Take. unfold zext_to,zext. rewrite rfa_reset_word_1_size subnn cats0. reflexivity.
 - exact Step.
Qed.
Theorem rfa_reset_history_1673 inputs path history limit :
 (forall t, (t < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history t) false (history t) flat_statements = Some (history (S t))) ->
 forall t, (4 <= t)%coq_nat -> (t <= limit)%coq_nat ->
 VM.find 1673 (history t) = Some (Gval (Fuint 32) (rfa_reset_word_1 inputs path)).
Proof.
 intros Steps t Lower Upper. destruct t as [|t]; [lia|].
 apply (rfa_reset_step_1673 inputs path (history t) (history t) (history (S t))).
 - apply (rfa_reset_history_1483 inputs path history limit Steps t);lia.
 - apply Steps;lia.
Qed.
Definition rfa_node_7371_expr := (@Eref VarOrder.T (@Eid VarOrder.T 1673)).
Definition rfa_node_7371_tail := match straight_drop 7543 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma rfa_node_7371_position : straight_drop 7542 flat_statements = Some (@Qcons VarOrder.T (@Snode VarOrder.T 7371 rfa_node_7371_expr) rfa_node_7371_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma rfa_node_7371_safe : formal_typed_suffix_safe flat_memories 7371 rfa_node_7371_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma rfa_node_7371_nonreg : has_register 7371 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem rfa_reset_step_7371 inputs path old current result :
 VM.find 1673 old = Some (Gval (Fuint 32) (rfa_reset_word_1 inputs path)) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 VM.find 7371 result = Some (Gval (Fuint 32) (rfa_reset_word_1 inputs path)).
Proof.
 intros Source Step.
 eapply formal_combinational_known_node;
 [exact rfa_node_7371_position|exact rfa_node_7371_safe|exact rfa_node_7371_nonreg| |reflexivity|exact Step].
 cbn [rfa_node_7371_expr eval_hfexpr_validif_policy eval_href_validif_policy]. exact Source.
Qed.
Theorem rfa_reset_history_7371 inputs path history limit :
 (forall t, (t < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history t) false (history t) flat_statements = Some (history (S t))) ->
 forall t, (5 <= t)%coq_nat -> (t <= limit)%coq_nat ->
 VM.find 7371 (history t) = Some (Gval (Fuint 32) (rfa_reset_word_1 inputs path)).
Proof.
 intros Steps t Lower Upper. destruct t as [|t]; [lia|].
 apply (rfa_reset_step_7371 inputs path (history t) (history t) (history (S t))).
 - apply (rfa_reset_history_1673 inputs path history limit Steps t);lia.
 - apply Steps;lia.
Qed.
Definition rfa_node_7372_expr := (@Eref VarOrder.T (@Eid VarOrder.T 7371)).
Definition rfa_node_7372_tail := match straight_drop 7544 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma rfa_node_7372_position : straight_drop 7543 flat_statements = Some (@Qcons VarOrder.T (@Snode VarOrder.T 7372 rfa_node_7372_expr) rfa_node_7372_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma rfa_node_7372_safe : formal_typed_suffix_safe flat_memories 7372 rfa_node_7372_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma rfa_node_7372_nonreg : has_register 7372 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem rfa_reset_step_7372 inputs path old current result :
 VM.find 7371 old = Some (Gval (Fuint 32) (rfa_reset_word_1 inputs path)) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 VM.find 7372 result = Some (Gval (Fuint 32) (rfa_reset_word_1 inputs path)).
Proof.
 intros Source Step.
 eapply formal_combinational_known_node;
 [exact rfa_node_7372_position|exact rfa_node_7372_safe|exact rfa_node_7372_nonreg| |reflexivity|exact Step].
 cbn [rfa_node_7372_expr eval_hfexpr_validif_policy eval_href_validif_policy]. exact Source.
Qed.
Theorem rfa_reset_history_7372 inputs path history limit :
 (forall t, (t < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history t) false (history t) flat_statements = Some (history (S t))) ->
 forall t, (6 <= t)%coq_nat -> (t <= limit)%coq_nat ->
 VM.find 7372 (history t) = Some (Gval (Fuint 32) (rfa_reset_word_1 inputs path)).
Proof.
 intros Steps t Lower Upper. destruct t as [|t]; [lia|].
 apply (rfa_reset_step_7372 inputs path (history t) (history t) (history (S t))).
 - apply (rfa_reset_history_7371 inputs path history limit Steps t);lia.
 - apply Steps;lia.
Qed.
Definition rfa_reset_word_2 inputs path := proj1_sig (formal_symbolic_inputs inputs path (validif_source_address (validif_raw_address nil 8599 0 nil)) nil 32).
Lemma rfa_reset_word_2_size inputs path : size (rfa_reset_word_2 inputs path) = 32%nat.
Proof. exact (proj2_sig (formal_symbolic_inputs inputs path (validif_source_address (validif_raw_address nil 8599 0 nil)) nil 32)). Qed.
Definition rfa_node_8093_expr := (@Evalidif VarOrder.T (@Econst VarOrder.T (Fuint 1) [::false]) (@Econst VarOrder.T (Fuint 32) [::false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false])).
Definition rfa_node_8093_tail := match straight_drop 8600 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma rfa_node_8093_position : straight_drop 8599 flat_statements = Some (@Qcons VarOrder.T (@Snode VarOrder.T 8093 rfa_node_8093_expr) rfa_node_8093_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma rfa_node_8093_safe : formal_typed_suffix_safe flat_memories 8093 rfa_node_8093_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma rfa_node_8093_nonreg : has_register 8093 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem rfa_reset_step_8093 inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 VM.find 8093 result = Some (Gval (Fuint 32) (rfa_reset_word_2 inputs path)).
Proof.
 intros Step.
 eapply formal_combinational_known_node;
 [exact rfa_node_8093_position|exact rfa_node_8093_safe|exact rfa_node_8093_nonreg| |reflexivity|exact Step].
 reflexivity.
Qed.
Theorem rfa_reset_history_8093 inputs path history limit :
 (forall t, (t < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history t) false (history t) flat_statements = Some (history (S t))) ->
 forall t, (1 <= t)%coq_nat -> (t <= limit)%coq_nat ->
 VM.find 8093 (history t) = Some (Gval (Fuint 32) (rfa_reset_word_2 inputs path)).
Proof.
 intros Steps t Lower Upper. destruct t as [|t]; [lia|].
 apply (rfa_reset_step_8093 inputs path (history t) (history t) (history (S t))).
 apply Steps;lia.
Qed.
Definition rfa_node_8094_expr := (@Eref VarOrder.T (@Eid VarOrder.T 8093)).
Definition rfa_node_8094_tail := match straight_drop 8601 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma rfa_node_8094_position : straight_drop 8600 flat_statements = Some (@Qcons VarOrder.T (@Snode VarOrder.T 8094 rfa_node_8094_expr) rfa_node_8094_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma rfa_node_8094_safe : formal_typed_suffix_safe flat_memories 8094 rfa_node_8094_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma rfa_node_8094_nonreg : has_register 8094 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem rfa_reset_step_8094 inputs path old current result :
 VM.find 8093 old = Some (Gval (Fuint 32) (rfa_reset_word_2 inputs path)) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 VM.find 8094 result = Some (Gval (Fuint 32) (rfa_reset_word_2 inputs path)).
Proof.
 intros Source Step.
 eapply formal_combinational_known_node;
 [exact rfa_node_8094_position|exact rfa_node_8094_safe|exact rfa_node_8094_nonreg| |reflexivity|exact Step].
 cbn [rfa_node_8094_expr eval_hfexpr_validif_policy eval_href_validif_policy]. exact Source.
Qed.
Theorem rfa_reset_history_8094 inputs path history limit :
 (forall t, (t < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history t) false (history t) flat_statements = Some (history (S t))) ->
 forall t, (2 <= t)%coq_nat -> (t <= limit)%coq_nat ->
 VM.find 8094 (history t) = Some (Gval (Fuint 32) (rfa_reset_word_2 inputs path)).
Proof.
 intros Steps t Lower Upper. destruct t as [|t]; [lia|].
 apply (rfa_reset_step_8094 inputs path (history t) (history t) (history (S t))).
 - apply (rfa_reset_history_8093 inputs path history limit Steps t);lia.
 - apply Steps;lia.
Qed.
Definition rfa_wire_789_decl := match straight_drop 799 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition rfa_wire_789_tail := match straight_drop 8807 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition rfa_wire_789_mid := take_statements 8007 rfa_wire_789_decl.
Lemma rfa_wire_789_position : straight_drop 798 flat_statements = Some (@Qcons VarOrder.T (@Swire VarOrder.T 789 (Gtyp (Fuint 32))) rfa_wire_789_decl).
Proof. vm_compute. reflexivity. Qed.
Lemma rfa_wire_789_split : rfa_wire_789_decl = statement_append rfa_wire_789_mid (@Qcons VarOrder.T (@Sfcnct VarOrder.T (@Eid VarOrder.T 789) (@Eref VarOrder.T (@Eid VarOrder.T 8094))) rfa_wire_789_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma rfa_wire_789_straight : straight_statements rfa_wire_789_mid.
Proof. vm_compute. exact I. Qed.
Lemma rfa_wire_789_mid_safe : formal_typed_suffix_safe flat_memories 789 rfa_wire_789_mid.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma rfa_wire_789_tail_safe : formal_typed_suffix_safe flat_memories 789 rfa_wire_789_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma rfa_wire_789_nonreg : has_register 789 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem rfa_reset_step_789 inputs path old current result :
 VM.find 8094 old = Some (Gval (Fuint 32) (rfa_reset_word_2 inputs path)) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 VM.find 789 result = Some (Gval (Fuint 32) (rfa_reset_word_2 inputs path)).
Proof.
 intros Source Step.
 apply (declared_connection_value 798 flat_statements rfa_wire_789_decl rfa_wire_789_mid rfa_wire_789_tail 789 8094 32
 (Gval (Fuint 32) (rfa_reset_word_2 inputs path)) (Gval (Fuint 32) (rfa_reset_word_2 inputs path))
 (formal_invalid_policy inputs path) flat_memories old current result rfa_wire_789_position rfa_wire_789_split rfa_wire_789_straight rfa_wire_789_mid_safe rfa_wire_789_tail_safe rfa_wire_789_nonreg (Logic.eq_refl _) Source).
 - assert (Take : take 32 (rfa_reset_word_2 inputs path) = rfa_reset_word_2 inputs path).
   { apply take_oversize. rewrite rfa_reset_word_2_size. reflexivity. }
   cbn [adapt_hvalue_as_type]. rewrite Take. unfold zext_to,zext. rewrite rfa_reset_word_2_size subnn cats0. reflexivity.
 - exact Step.
Qed.
Theorem rfa_reset_history_789 inputs path history limit :
 (forall t, (t < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history t) false (history t) flat_statements = Some (history (S t))) ->
 forall t, (3 <= t)%coq_nat -> (t <= limit)%coq_nat ->
 VM.find 789 (history t) = Some (Gval (Fuint 32) (rfa_reset_word_2 inputs path)).
Proof.
 intros Steps t Lower Upper. destruct t as [|t]; [lia|].
 apply (rfa_reset_step_789 inputs path (history t) (history t) (history (S t))).
 - apply (rfa_reset_history_8094 inputs path history limit Steps t);lia.
 - apply Steps;lia.
Qed.
Definition rfa_node_1087_expr := (@Eref VarOrder.T (@Eid VarOrder.T 789)).
Definition rfa_node_1087_tail := match straight_drop 1097 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma rfa_node_1087_position : straight_drop 1096 flat_statements = Some (@Qcons VarOrder.T (@Snode VarOrder.T 1087 rfa_node_1087_expr) rfa_node_1087_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma rfa_node_1087_safe : formal_typed_suffix_safe flat_memories 1087 rfa_node_1087_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma rfa_node_1087_nonreg : has_register 1087 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem rfa_reset_step_1087 inputs path old current result :
 VM.find 789 old = Some (Gval (Fuint 32) (rfa_reset_word_2 inputs path)) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 VM.find 1087 result = Some (Gval (Fuint 32) (rfa_reset_word_2 inputs path)).
Proof.
 intros Source Step.
 eapply formal_combinational_known_node;
 [exact rfa_node_1087_position|exact rfa_node_1087_safe|exact rfa_node_1087_nonreg| |reflexivity|exact Step].
 cbn [rfa_node_1087_expr eval_hfexpr_validif_policy eval_href_validif_policy]. exact Source.
Qed.
Theorem rfa_reset_history_1087 inputs path history limit :
 (forall t, (t < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history t) false (history t) flat_statements = Some (history (S t))) ->
 forall t, (4 <= t)%coq_nat -> (t <= limit)%coq_nat ->
 VM.find 1087 (history t) = Some (Gval (Fuint 32) (rfa_reset_word_2 inputs path)).
Proof.
 intros Steps t Lower Upper. destruct t as [|t]; [lia|].
 apply (rfa_reset_step_1087 inputs path (history t) (history t) (history (S t))).
 - apply (rfa_reset_history_789 inputs path history limit Steps t);lia.
 - apply Steps;lia.
Qed.
Definition rfa_wire_1484_decl := match straight_drop 1564 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition rfa_wire_1484_tail := match straight_drop 8973 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition rfa_wire_1484_mid := take_statements 7408 rfa_wire_1484_decl.
Lemma rfa_wire_1484_position : straight_drop 1563 flat_statements = Some (@Qcons VarOrder.T (@Swire VarOrder.T 1484 (Gtyp (Fuint 32))) rfa_wire_1484_decl).
Proof. vm_compute. reflexivity. Qed.
Lemma rfa_wire_1484_split : rfa_wire_1484_decl = statement_append rfa_wire_1484_mid (@Qcons VarOrder.T (@Sfcnct VarOrder.T (@Eid VarOrder.T 1484) (@Eref VarOrder.T (@Eid VarOrder.T 8094))) rfa_wire_1484_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma rfa_wire_1484_straight : straight_statements rfa_wire_1484_mid.
Proof. vm_compute. exact I. Qed.
Lemma rfa_wire_1484_mid_safe : formal_typed_suffix_safe flat_memories 1484 rfa_wire_1484_mid.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma rfa_wire_1484_tail_safe : formal_typed_suffix_safe flat_memories 1484 rfa_wire_1484_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma rfa_wire_1484_nonreg : has_register 1484 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem rfa_reset_step_1484 inputs path old current result :
 VM.find 8094 old = Some (Gval (Fuint 32) (rfa_reset_word_2 inputs path)) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 VM.find 1484 result = Some (Gval (Fuint 32) (rfa_reset_word_2 inputs path)).
Proof.
 intros Source Step.
 apply (declared_connection_value 1563 flat_statements rfa_wire_1484_decl rfa_wire_1484_mid rfa_wire_1484_tail 1484 8094 32
 (Gval (Fuint 32) (rfa_reset_word_2 inputs path)) (Gval (Fuint 32) (rfa_reset_word_2 inputs path))
 (formal_invalid_policy inputs path) flat_memories old current result rfa_wire_1484_position rfa_wire_1484_split rfa_wire_1484_straight rfa_wire_1484_mid_safe rfa_wire_1484_tail_safe rfa_wire_1484_nonreg (Logic.eq_refl _) Source).
 - assert (Take : take 32 (rfa_reset_word_2 inputs path) = rfa_reset_word_2 inputs path).
   { apply take_oversize. rewrite rfa_reset_word_2_size. reflexivity. }
   cbn [adapt_hvalue_as_type]. rewrite Take. unfold zext_to,zext. rewrite rfa_reset_word_2_size subnn cats0. reflexivity.
 - exact Step.
Qed.
Theorem rfa_reset_history_1484 inputs path history limit :
 (forall t, (t < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history t) false (history t) flat_statements = Some (history (S t))) ->
 forall t, (3 <= t)%coq_nat -> (t <= limit)%coq_nat ->
 VM.find 1484 (history t) = Some (Gval (Fuint 32) (rfa_reset_word_2 inputs path)).
Proof.
 intros Steps t Lower Upper. destruct t as [|t]; [lia|].
 apply (rfa_reset_step_1484 inputs path (history t) (history t) (history (S t))).
 - apply (rfa_reset_history_8094 inputs path history limit Steps t);lia.
 - apply Steps;lia.
Qed.
Definition rfa_wire_1674_decl := match straight_drop 1754 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition rfa_wire_1674_tail := match straight_drop 8225 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition rfa_wire_1674_mid := take_statements 6470 rfa_wire_1674_decl.
Lemma rfa_wire_1674_position : straight_drop 1753 flat_statements = Some (@Qcons VarOrder.T (@Swire VarOrder.T 1674 (Gtyp (Fuint 32))) rfa_wire_1674_decl).
Proof. vm_compute. reflexivity. Qed.
Lemma rfa_wire_1674_split : rfa_wire_1674_decl = statement_append rfa_wire_1674_mid (@Qcons VarOrder.T (@Sfcnct VarOrder.T (@Eid VarOrder.T 1674) (@Eref VarOrder.T (@Eid VarOrder.T 1484))) rfa_wire_1674_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma rfa_wire_1674_straight : straight_statements rfa_wire_1674_mid.
Proof. vm_compute. exact I. Qed.
Lemma rfa_wire_1674_mid_safe : formal_typed_suffix_safe flat_memories 1674 rfa_wire_1674_mid.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma rfa_wire_1674_tail_safe : formal_typed_suffix_safe flat_memories 1674 rfa_wire_1674_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma rfa_wire_1674_nonreg : has_register 1674 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem rfa_reset_step_1674 inputs path old current result :
 VM.find 1484 old = Some (Gval (Fuint 32) (rfa_reset_word_2 inputs path)) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 VM.find 1674 result = Some (Gval (Fuint 32) (rfa_reset_word_2 inputs path)).
Proof.
 intros Source Step.
 apply (declared_connection_value 1753 flat_statements rfa_wire_1674_decl rfa_wire_1674_mid rfa_wire_1674_tail 1674 1484 32
 (Gval (Fuint 32) (rfa_reset_word_2 inputs path)) (Gval (Fuint 32) (rfa_reset_word_2 inputs path))
 (formal_invalid_policy inputs path) flat_memories old current result rfa_wire_1674_position rfa_wire_1674_split rfa_wire_1674_straight rfa_wire_1674_mid_safe rfa_wire_1674_tail_safe rfa_wire_1674_nonreg (Logic.eq_refl _) Source).
 - assert (Take : take 32 (rfa_reset_word_2 inputs path) = rfa_reset_word_2 inputs path).
   { apply take_oversize. rewrite rfa_reset_word_2_size. reflexivity. }
   cbn [adapt_hvalue_as_type]. rewrite Take. unfold zext_to,zext. rewrite rfa_reset_word_2_size subnn cats0. reflexivity.
 - exact Step.
Qed.
Theorem rfa_reset_history_1674 inputs path history limit :
 (forall t, (t < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history t) false (history t) flat_statements = Some (history (S t))) ->
 forall t, (4 <= t)%coq_nat -> (t <= limit)%coq_nat ->
 VM.find 1674 (history t) = Some (Gval (Fuint 32) (rfa_reset_word_2 inputs path)).
Proof.
 intros Steps t Lower Upper. destruct t as [|t]; [lia|].
 apply (rfa_reset_step_1674 inputs path (history t) (history t) (history (S t))).
 - apply (rfa_reset_history_1484 inputs path history limit Steps t);lia.
 - apply Steps;lia.
Qed.
Definition rfa_node_7373_expr := (@Eref VarOrder.T (@Eid VarOrder.T 1674)).
Definition rfa_node_7373_tail := match straight_drop 7545 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma rfa_node_7373_position : straight_drop 7544 flat_statements = Some (@Qcons VarOrder.T (@Snode VarOrder.T 7373 rfa_node_7373_expr) rfa_node_7373_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma rfa_node_7373_safe : formal_typed_suffix_safe flat_memories 7373 rfa_node_7373_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma rfa_node_7373_nonreg : has_register 7373 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem rfa_reset_step_7373 inputs path old current result :
 VM.find 1674 old = Some (Gval (Fuint 32) (rfa_reset_word_2 inputs path)) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 VM.find 7373 result = Some (Gval (Fuint 32) (rfa_reset_word_2 inputs path)).
Proof.
 intros Source Step.
 eapply formal_combinational_known_node;
 [exact rfa_node_7373_position|exact rfa_node_7373_safe|exact rfa_node_7373_nonreg| |reflexivity|exact Step].
 cbn [rfa_node_7373_expr eval_hfexpr_validif_policy eval_href_validif_policy]. exact Source.
Qed.
Theorem rfa_reset_history_7373 inputs path history limit :
 (forall t, (t < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history t) false (history t) flat_statements = Some (history (S t))) ->
 forall t, (5 <= t)%coq_nat -> (t <= limit)%coq_nat ->
 VM.find 7373 (history t) = Some (Gval (Fuint 32) (rfa_reset_word_2 inputs path)).
Proof.
 intros Steps t Lower Upper. destruct t as [|t]; [lia|].
 apply (rfa_reset_step_7373 inputs path (history t) (history t) (history (S t))).
 - apply (rfa_reset_history_1674 inputs path history limit Steps t);lia.
 - apply Steps;lia.
Qed.
Definition rfa_node_7374_expr := (@Eref VarOrder.T (@Eid VarOrder.T 7373)).
Definition rfa_node_7374_tail := match straight_drop 7546 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma rfa_node_7374_position : straight_drop 7545 flat_statements = Some (@Qcons VarOrder.T (@Snode VarOrder.T 7374 rfa_node_7374_expr) rfa_node_7374_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma rfa_node_7374_safe : formal_typed_suffix_safe flat_memories 7374 rfa_node_7374_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma rfa_node_7374_nonreg : has_register 7374 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem rfa_reset_step_7374 inputs path old current result :
 VM.find 7373 old = Some (Gval (Fuint 32) (rfa_reset_word_2 inputs path)) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 VM.find 7374 result = Some (Gval (Fuint 32) (rfa_reset_word_2 inputs path)).
Proof.
 intros Source Step.
 eapply formal_combinational_known_node;
 [exact rfa_node_7374_position|exact rfa_node_7374_safe|exact rfa_node_7374_nonreg| |reflexivity|exact Step].
 cbn [rfa_node_7374_expr eval_hfexpr_validif_policy eval_href_validif_policy]. exact Source.
Qed.
Theorem rfa_reset_history_7374 inputs path history limit :
 (forall t, (t < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history t) false (history t) flat_statements = Some (history (S t))) ->
 forall t, (6 <= t)%coq_nat -> (t <= limit)%coq_nat ->
 VM.find 7374 (history t) = Some (Gval (Fuint 32) (rfa_reset_word_2 inputs path)).
Proof.
 intros Steps t Lower Upper. destruct t as [|t]; [lia|].
 apply (rfa_reset_step_7374 inputs path (history t) (history t) (history (S t))).
 - apply (rfa_reset_history_7373 inputs path history limit Steps t);lia.
 - apply Steps;lia.
Qed.
Definition rfa_reset_word_3 inputs path := proj1_sig (formal_symbolic_inputs inputs path (validif_source_address (validif_raw_address nil 8601 0 nil)) nil 32).
Lemma rfa_reset_word_3_size inputs path : size (rfa_reset_word_3 inputs path) = 32%nat.
Proof. exact (proj2_sig (formal_symbolic_inputs inputs path (validif_source_address (validif_raw_address nil 8601 0 nil)) nil 32)). Qed.
Definition rfa_node_8095_expr := (@Evalidif VarOrder.T (@Econst VarOrder.T (Fuint 1) [::false]) (@Econst VarOrder.T (Fuint 32) [::false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false])).
Definition rfa_node_8095_tail := match straight_drop 8602 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma rfa_node_8095_position : straight_drop 8601 flat_statements = Some (@Qcons VarOrder.T (@Snode VarOrder.T 8095 rfa_node_8095_expr) rfa_node_8095_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma rfa_node_8095_safe : formal_typed_suffix_safe flat_memories 8095 rfa_node_8095_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma rfa_node_8095_nonreg : has_register 8095 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem rfa_reset_step_8095 inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 VM.find 8095 result = Some (Gval (Fuint 32) (rfa_reset_word_3 inputs path)).
Proof.
 intros Step.
 eapply formal_combinational_known_node;
 [exact rfa_node_8095_position|exact rfa_node_8095_safe|exact rfa_node_8095_nonreg| |reflexivity|exact Step].
 reflexivity.
Qed.
Theorem rfa_reset_history_8095 inputs path history limit :
 (forall t, (t < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history t) false (history t) flat_statements = Some (history (S t))) ->
 forall t, (1 <= t)%coq_nat -> (t <= limit)%coq_nat ->
 VM.find 8095 (history t) = Some (Gval (Fuint 32) (rfa_reset_word_3 inputs path)).
Proof.
 intros Steps t Lower Upper. destruct t as [|t]; [lia|].
 apply (rfa_reset_step_8095 inputs path (history t) (history t) (history (S t))).
 apply Steps;lia.
Qed.
Definition rfa_node_8096_expr := (@Eref VarOrder.T (@Eid VarOrder.T 8095)).
Definition rfa_node_8096_tail := match straight_drop 8603 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma rfa_node_8096_position : straight_drop 8602 flat_statements = Some (@Qcons VarOrder.T (@Snode VarOrder.T 8096 rfa_node_8096_expr) rfa_node_8096_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma rfa_node_8096_safe : formal_typed_suffix_safe flat_memories 8096 rfa_node_8096_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma rfa_node_8096_nonreg : has_register 8096 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem rfa_reset_step_8096 inputs path old current result :
 VM.find 8095 old = Some (Gval (Fuint 32) (rfa_reset_word_3 inputs path)) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 VM.find 8096 result = Some (Gval (Fuint 32) (rfa_reset_word_3 inputs path)).
Proof.
 intros Source Step.
 eapply formal_combinational_known_node;
 [exact rfa_node_8096_position|exact rfa_node_8096_safe|exact rfa_node_8096_nonreg| |reflexivity|exact Step].
 cbn [rfa_node_8096_expr eval_hfexpr_validif_policy eval_href_validif_policy]. exact Source.
Qed.
Theorem rfa_reset_history_8096 inputs path history limit :
 (forall t, (t < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history t) false (history t) flat_statements = Some (history (S t))) ->
 forall t, (2 <= t)%coq_nat -> (t <= limit)%coq_nat ->
 VM.find 8096 (history t) = Some (Gval (Fuint 32) (rfa_reset_word_3 inputs path)).
Proof.
 intros Steps t Lower Upper. destruct t as [|t]; [lia|].
 apply (rfa_reset_step_8096 inputs path (history t) (history t) (history (S t))).
 - apply (rfa_reset_history_8095 inputs path history limit Steps t);lia.
 - apply Steps;lia.
Qed.
Definition rfa_wire_790_decl := match straight_drop 800 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition rfa_wire_790_tail := match straight_drop 8808 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition rfa_wire_790_mid := take_statements 8007 rfa_wire_790_decl.
Lemma rfa_wire_790_position : straight_drop 799 flat_statements = Some (@Qcons VarOrder.T (@Swire VarOrder.T 790 (Gtyp (Fuint 32))) rfa_wire_790_decl).
Proof. vm_compute. reflexivity. Qed.
Lemma rfa_wire_790_split : rfa_wire_790_decl = statement_append rfa_wire_790_mid (@Qcons VarOrder.T (@Sfcnct VarOrder.T (@Eid VarOrder.T 790) (@Eref VarOrder.T (@Eid VarOrder.T 8096))) rfa_wire_790_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma rfa_wire_790_straight : straight_statements rfa_wire_790_mid.
Proof. vm_compute. exact I. Qed.
Lemma rfa_wire_790_mid_safe : formal_typed_suffix_safe flat_memories 790 rfa_wire_790_mid.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma rfa_wire_790_tail_safe : formal_typed_suffix_safe flat_memories 790 rfa_wire_790_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma rfa_wire_790_nonreg : has_register 790 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem rfa_reset_step_790 inputs path old current result :
 VM.find 8096 old = Some (Gval (Fuint 32) (rfa_reset_word_3 inputs path)) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 VM.find 790 result = Some (Gval (Fuint 32) (rfa_reset_word_3 inputs path)).
Proof.
 intros Source Step.
 apply (declared_connection_value 799 flat_statements rfa_wire_790_decl rfa_wire_790_mid rfa_wire_790_tail 790 8096 32
 (Gval (Fuint 32) (rfa_reset_word_3 inputs path)) (Gval (Fuint 32) (rfa_reset_word_3 inputs path))
 (formal_invalid_policy inputs path) flat_memories old current result rfa_wire_790_position rfa_wire_790_split rfa_wire_790_straight rfa_wire_790_mid_safe rfa_wire_790_tail_safe rfa_wire_790_nonreg (Logic.eq_refl _) Source).
 - assert (Take : take 32 (rfa_reset_word_3 inputs path) = rfa_reset_word_3 inputs path).
   { apply take_oversize. rewrite rfa_reset_word_3_size. reflexivity. }
   cbn [adapt_hvalue_as_type]. rewrite Take. unfold zext_to,zext. rewrite rfa_reset_word_3_size subnn cats0. reflexivity.
 - exact Step.
Qed.
Theorem rfa_reset_history_790 inputs path history limit :
 (forall t, (t < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history t) false (history t) flat_statements = Some (history (S t))) ->
 forall t, (3 <= t)%coq_nat -> (t <= limit)%coq_nat ->
 VM.find 790 (history t) = Some (Gval (Fuint 32) (rfa_reset_word_3 inputs path)).
Proof.
 intros Steps t Lower Upper. destruct t as [|t]; [lia|].
 apply (rfa_reset_step_790 inputs path (history t) (history t) (history (S t))).
 - apply (rfa_reset_history_8096 inputs path history limit Steps t);lia.
 - apply Steps;lia.
Qed.
Definition rfa_node_1088_expr := (@Eref VarOrder.T (@Eid VarOrder.T 790)).
Definition rfa_node_1088_tail := match straight_drop 1098 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma rfa_node_1088_position : straight_drop 1097 flat_statements = Some (@Qcons VarOrder.T (@Snode VarOrder.T 1088 rfa_node_1088_expr) rfa_node_1088_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma rfa_node_1088_safe : formal_typed_suffix_safe flat_memories 1088 rfa_node_1088_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma rfa_node_1088_nonreg : has_register 1088 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem rfa_reset_step_1088 inputs path old current result :
 VM.find 790 old = Some (Gval (Fuint 32) (rfa_reset_word_3 inputs path)) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 VM.find 1088 result = Some (Gval (Fuint 32) (rfa_reset_word_3 inputs path)).
Proof.
 intros Source Step.
 eapply formal_combinational_known_node;
 [exact rfa_node_1088_position|exact rfa_node_1088_safe|exact rfa_node_1088_nonreg| |reflexivity|exact Step].
 cbn [rfa_node_1088_expr eval_hfexpr_validif_policy eval_href_validif_policy]. exact Source.
Qed.
Theorem rfa_reset_history_1088 inputs path history limit :
 (forall t, (t < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history t) false (history t) flat_statements = Some (history (S t))) ->
 forall t, (4 <= t)%coq_nat -> (t <= limit)%coq_nat ->
 VM.find 1088 (history t) = Some (Gval (Fuint 32) (rfa_reset_word_3 inputs path)).
Proof.
 intros Steps t Lower Upper. destruct t as [|t]; [lia|].
 apply (rfa_reset_step_1088 inputs path (history t) (history t) (history (S t))).
 - apply (rfa_reset_history_790 inputs path history limit Steps t);lia.
 - apply Steps;lia.
Qed.
Definition rfa_wire_1485_decl := match straight_drop 1565 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition rfa_wire_1485_tail := match straight_drop 8974 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition rfa_wire_1485_mid := take_statements 7408 rfa_wire_1485_decl.
Lemma rfa_wire_1485_position : straight_drop 1564 flat_statements = Some (@Qcons VarOrder.T (@Swire VarOrder.T 1485 (Gtyp (Fuint 32))) rfa_wire_1485_decl).
Proof. vm_compute. reflexivity. Qed.
Lemma rfa_wire_1485_split : rfa_wire_1485_decl = statement_append rfa_wire_1485_mid (@Qcons VarOrder.T (@Sfcnct VarOrder.T (@Eid VarOrder.T 1485) (@Eref VarOrder.T (@Eid VarOrder.T 8096))) rfa_wire_1485_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma rfa_wire_1485_straight : straight_statements rfa_wire_1485_mid.
Proof. vm_compute. exact I. Qed.
Lemma rfa_wire_1485_mid_safe : formal_typed_suffix_safe flat_memories 1485 rfa_wire_1485_mid.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma rfa_wire_1485_tail_safe : formal_typed_suffix_safe flat_memories 1485 rfa_wire_1485_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma rfa_wire_1485_nonreg : has_register 1485 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem rfa_reset_step_1485 inputs path old current result :
 VM.find 8096 old = Some (Gval (Fuint 32) (rfa_reset_word_3 inputs path)) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 VM.find 1485 result = Some (Gval (Fuint 32) (rfa_reset_word_3 inputs path)).
Proof.
 intros Source Step.
 apply (declared_connection_value 1564 flat_statements rfa_wire_1485_decl rfa_wire_1485_mid rfa_wire_1485_tail 1485 8096 32
 (Gval (Fuint 32) (rfa_reset_word_3 inputs path)) (Gval (Fuint 32) (rfa_reset_word_3 inputs path))
 (formal_invalid_policy inputs path) flat_memories old current result rfa_wire_1485_position rfa_wire_1485_split rfa_wire_1485_straight rfa_wire_1485_mid_safe rfa_wire_1485_tail_safe rfa_wire_1485_nonreg (Logic.eq_refl _) Source).
 - assert (Take : take 32 (rfa_reset_word_3 inputs path) = rfa_reset_word_3 inputs path).
   { apply take_oversize. rewrite rfa_reset_word_3_size. reflexivity. }
   cbn [adapt_hvalue_as_type]. rewrite Take. unfold zext_to,zext. rewrite rfa_reset_word_3_size subnn cats0. reflexivity.
 - exact Step.
Qed.
Theorem rfa_reset_history_1485 inputs path history limit :
 (forall t, (t < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history t) false (history t) flat_statements = Some (history (S t))) ->
 forall t, (3 <= t)%coq_nat -> (t <= limit)%coq_nat ->
 VM.find 1485 (history t) = Some (Gval (Fuint 32) (rfa_reset_word_3 inputs path)).
Proof.
 intros Steps t Lower Upper. destruct t as [|t]; [lia|].
 apply (rfa_reset_step_1485 inputs path (history t) (history t) (history (S t))).
 - apply (rfa_reset_history_8096 inputs path history limit Steps t);lia.
 - apply Steps;lia.
Qed.
Definition rfa_wire_1675_decl := match straight_drop 1755 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition rfa_wire_1675_tail := match straight_drop 8226 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition rfa_wire_1675_mid := take_statements 6470 rfa_wire_1675_decl.
Lemma rfa_wire_1675_position : straight_drop 1754 flat_statements = Some (@Qcons VarOrder.T (@Swire VarOrder.T 1675 (Gtyp (Fuint 32))) rfa_wire_1675_decl).
Proof. vm_compute. reflexivity. Qed.
Lemma rfa_wire_1675_split : rfa_wire_1675_decl = statement_append rfa_wire_1675_mid (@Qcons VarOrder.T (@Sfcnct VarOrder.T (@Eid VarOrder.T 1675) (@Eref VarOrder.T (@Eid VarOrder.T 1485))) rfa_wire_1675_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma rfa_wire_1675_straight : straight_statements rfa_wire_1675_mid.
Proof. vm_compute. exact I. Qed.
Lemma rfa_wire_1675_mid_safe : formal_typed_suffix_safe flat_memories 1675 rfa_wire_1675_mid.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma rfa_wire_1675_tail_safe : formal_typed_suffix_safe flat_memories 1675 rfa_wire_1675_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma rfa_wire_1675_nonreg : has_register 1675 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem rfa_reset_step_1675 inputs path old current result :
 VM.find 1485 old = Some (Gval (Fuint 32) (rfa_reset_word_3 inputs path)) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 VM.find 1675 result = Some (Gval (Fuint 32) (rfa_reset_word_3 inputs path)).
Proof.
 intros Source Step.
 apply (declared_connection_value 1754 flat_statements rfa_wire_1675_decl rfa_wire_1675_mid rfa_wire_1675_tail 1675 1485 32
 (Gval (Fuint 32) (rfa_reset_word_3 inputs path)) (Gval (Fuint 32) (rfa_reset_word_3 inputs path))
 (formal_invalid_policy inputs path) flat_memories old current result rfa_wire_1675_position rfa_wire_1675_split rfa_wire_1675_straight rfa_wire_1675_mid_safe rfa_wire_1675_tail_safe rfa_wire_1675_nonreg (Logic.eq_refl _) Source).
 - assert (Take : take 32 (rfa_reset_word_3 inputs path) = rfa_reset_word_3 inputs path).
   { apply take_oversize. rewrite rfa_reset_word_3_size. reflexivity. }
   cbn [adapt_hvalue_as_type]. rewrite Take. unfold zext_to,zext. rewrite rfa_reset_word_3_size subnn cats0. reflexivity.
 - exact Step.
Qed.
Theorem rfa_reset_history_1675 inputs path history limit :
 (forall t, (t < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history t) false (history t) flat_statements = Some (history (S t))) ->
 forall t, (4 <= t)%coq_nat -> (t <= limit)%coq_nat ->
 VM.find 1675 (history t) = Some (Gval (Fuint 32) (rfa_reset_word_3 inputs path)).
Proof.
 intros Steps t Lower Upper. destruct t as [|t]; [lia|].
 apply (rfa_reset_step_1675 inputs path (history t) (history t) (history (S t))).
 - apply (rfa_reset_history_1485 inputs path history limit Steps t);lia.
 - apply Steps;lia.
Qed.
Definition rfa_node_7375_expr := (@Eref VarOrder.T (@Eid VarOrder.T 1675)).
Definition rfa_node_7375_tail := match straight_drop 7547 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma rfa_node_7375_position : straight_drop 7546 flat_statements = Some (@Qcons VarOrder.T (@Snode VarOrder.T 7375 rfa_node_7375_expr) rfa_node_7375_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma rfa_node_7375_safe : formal_typed_suffix_safe flat_memories 7375 rfa_node_7375_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma rfa_node_7375_nonreg : has_register 7375 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem rfa_reset_step_7375 inputs path old current result :
 VM.find 1675 old = Some (Gval (Fuint 32) (rfa_reset_word_3 inputs path)) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 VM.find 7375 result = Some (Gval (Fuint 32) (rfa_reset_word_3 inputs path)).
Proof.
 intros Source Step.
 eapply formal_combinational_known_node;
 [exact rfa_node_7375_position|exact rfa_node_7375_safe|exact rfa_node_7375_nonreg| |reflexivity|exact Step].
 cbn [rfa_node_7375_expr eval_hfexpr_validif_policy eval_href_validif_policy]. exact Source.
Qed.
Theorem rfa_reset_history_7375 inputs path history limit :
 (forall t, (t < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history t) false (history t) flat_statements = Some (history (S t))) ->
 forall t, (5 <= t)%coq_nat -> (t <= limit)%coq_nat ->
 VM.find 7375 (history t) = Some (Gval (Fuint 32) (rfa_reset_word_3 inputs path)).
Proof.
 intros Steps t Lower Upper. destruct t as [|t]; [lia|].
 apply (rfa_reset_step_7375 inputs path (history t) (history t) (history (S t))).
 - apply (rfa_reset_history_1675 inputs path history limit Steps t);lia.
 - apply Steps;lia.
Qed.
Definition rfa_node_7376_expr := (@Eref VarOrder.T (@Eid VarOrder.T 7375)).
Definition rfa_node_7376_tail := match straight_drop 7548 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma rfa_node_7376_position : straight_drop 7547 flat_statements = Some (@Qcons VarOrder.T (@Snode VarOrder.T 7376 rfa_node_7376_expr) rfa_node_7376_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma rfa_node_7376_safe : formal_typed_suffix_safe flat_memories 7376 rfa_node_7376_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma rfa_node_7376_nonreg : has_register 7376 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem rfa_reset_step_7376 inputs path old current result :
 VM.find 7375 old = Some (Gval (Fuint 32) (rfa_reset_word_3 inputs path)) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 VM.find 7376 result = Some (Gval (Fuint 32) (rfa_reset_word_3 inputs path)).
Proof.
 intros Source Step.
 eapply formal_combinational_known_node;
 [exact rfa_node_7376_position|exact rfa_node_7376_safe|exact rfa_node_7376_nonreg| |reflexivity|exact Step].
 cbn [rfa_node_7376_expr eval_hfexpr_validif_policy eval_href_validif_policy]. exact Source.
Qed.
Theorem rfa_reset_history_7376 inputs path history limit :
 (forall t, (t < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history t) false (history t) flat_statements = Some (history (S t))) ->
 forall t, (6 <= t)%coq_nat -> (t <= limit)%coq_nat ->
 VM.find 7376 (history t) = Some (Gval (Fuint 32) (rfa_reset_word_3 inputs path)).
Proof.
 intros Steps t Lower Upper. destruct t as [|t]; [lia|].
 apply (rfa_reset_step_7376 inputs path (history t) (history t) (history (S t))).
 - apply (rfa_reset_history_7375 inputs path history limit Steps t);lia.
 - apply Steps;lia.
Qed.
