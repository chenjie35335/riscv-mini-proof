Require Import ReferenceLoadSemantics DUTRedirectSemantics FetchPCArithmetic ALUAddressSemantics ALUOutputTransfer ReferenceRedirectSpine JointUpdateNodePositions JointUpdateExpressionCertificates JointUpdateConnectionCertificates FormalDeclaredConnection ReferenceLoadImmediate CoreSocModel ComparisonNodes.
From Coq Require Import NArith ZArith List Lia.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From nbits Require Import NBits.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Local Opaque flat_statements flat_memories generated_modules generated_top.
Definition rf_negated_word right :=take 32(from_Z 33(-to_Zpos right)%Z).
Lemma rf_negated_word_size right :size(rf_negated_word right)=32%nat.
Proof. unfold rf_negated_word. rewrite size_take size_from_Z;reflexivity. Qed.
Lemma rf_add_word_addB left right :size left=32%nat ->size right=32%nat ->reference_load_address left right=addB left right.
Proof.
 intros Left Right. unfold reference_load_address. rewrite(fetch_pc_take_from_N 33 32 _ (Logic.eq_refl true)).
 apply to_Zpos_inj_ss.
 - rewrite size_from_N size_addB Left Right;reflexivity.
 - rewrite !to_Zpos_N to_N_from_N(to_N_addB (bs1:=left) (bs2:=right) ltac:(lia))Left;reflexivity.
Qed.
Lemma rf_negated_word_subB right :size right=32%nat ->rf_negated_word right=subB(zeros 32)right.
Proof.
 intro Size.
 change(dut_branch_difference(zeros 32)right=subB(zeros 32)right).
 apply dut_branch_difference_subB;[apply size_zeros|exact Size].
Qed.
Lemma rf_subtract_sum left right :size left=32%nat ->size right=32%nat ->
 reference_load_address left(rf_negated_word right)=dut_branch_difference left right.
Proof.
 intros Left Right.
 rewrite(rf_add_word_addB left _ Left(rf_negated_word_size right))(rf_negated_word_subB right Right).
 rewrite -Right sub0B(dut_branch_difference_subB left right Left Right).
 symmetry;apply/eqP;apply subB_equiv_addB_negB;apply/eqP;lia.
Qed.
Theorem rf_alu_negated_value invalid s0 s1 s2 right :
 VM.find 1152 s0=Some(Gval(Fuint 32)right) ->
 formal_value_iter invalid flat_memories s0 false s0 flat_statements=Some s1 ->
 formal_value_iter invalid flat_memories s1 false s1 flat_statements=Some s2 ->
 VM.find 1158 s2=Some(Gval(Fuint 32)(rf_negated_word right)).
Proof.
 intros Right S1 S2.
 assert(Neg:VM.find 1157 s1=Some(Gval(Fuint 33)(from_Z 33(-to_Zpos right)%Z))).
 { eapply(reference_redirect_ground_step alu_address_offsets alu_address_nodes 1157 alu_address_expr_1157);
 [exact alu_address_positions|exact alu_address_safety|apply(List.nth_error_In alu_address_nodes 1%nat);reflexivity| |exact S1].
 intro site. cbn[alu_address_expr_1157 eval_hfexpr_validif_policy eval_href_validif_policy]. rewrite Right. reflexivity. }
 eapply(reference_redirect_ground_step alu_address_offsets alu_address_nodes 1158 alu_address_expr_1158);
 [exact alu_address_positions|exact alu_address_safety|apply(List.nth_error_In alu_address_nodes 2%nat);reflexivity| |exact S2].
 intro site. cbn[alu_address_expr_1158 eval_hfexpr_validif_policy eval_href_validif_policy]. rewrite Neg. reflexivity.
Qed.
Theorem rf_alu_select_sub invalid s0 s1 s2 right :
 VM.find 1153 s0=Some(Gval(Fuint 4)[::true;false;false;false]) ->
 VM.find 1152 s1=Some(Gval(Fuint 32)right) ->VM.find 1158 s1=Some(Gval(Fuint 32)(rf_negated_word right)) ->
 formal_value_iter invalid flat_memories s0 false s0 flat_statements=Some s1 ->
 formal_value_iter invalid flat_memories s1 false s1 flat_statements=Some s2 ->
 VM.find 1159 s2=Some(Gval(Fuint 32)(rf_negated_word right)).
Proof.
 intros Mode Right Neg S1 S2.
 assert(Guard:VM.find 1156 s1=Some(Gval(Fuint 1)[::true])).
 { eapply(reference_redirect_ground_step alu_address_offsets alu_address_nodes 1156 alu_address_expr_1156);
 [exact alu_address_positions|exact alu_address_safety|apply(List.nth_error_In alu_address_nodes 0%nat);reflexivity| |exact S1].
 intro site. cbn[alu_address_expr_1156 eval_hfexpr_validif_policy eval_href_validif_policy]. rewrite Mode;reflexivity. }
 eapply(reference_redirect_ground_step alu_address_offsets alu_address_nodes 1159 alu_address_expr_1159);
 [exact alu_address_positions|exact alu_address_safety|apply(List.nth_error_In alu_address_nodes 3%nat);reflexivity| |exact S2].
 intro site. unfold alu_address_expr_1159.
 exact(immediate_selected_mux _ site s1 1156 1158 1152 32(rf_negated_word right)(Gval(Fuint 32)right)true(rf_negated_word_size right)Guard Neg Right(Logic.eq_refl _)).
Qed.
Theorem rf_alu_output_sum_history sub invalid s0 s1 s2 s3 s4 word :
 size word = 32%nat ->
 VM.find 1153 s0 = Some (Gval (Fuint 4) [::sub;false;false;false]) ->
 VM.find 1161 s2 = Some (Gval (Fuint 32) word) ->
 formal_value_iter invalid flat_memories s0 false s0 flat_statements = Some s1 ->
 formal_value_iter invalid flat_memories s1 false s1 flat_statements = Some s2 ->
 formal_value_iter invalid flat_memories s2 false s2 flat_statements = Some s3 ->
 formal_value_iter invalid flat_memories s3 false s3 flat_statements = Some s4 ->
 VM.find 1154 s4 = Some (Gval (Fuint 32) word).
Proof.
 intros Size Mode Sum S1 S2 S3 S4.
 assert (H1279 : VM.find 1279 s1 = Some (Gval (Fuint 1) [::negb sub])).
 { eapply (reference_redirect_ground_step joint_update_node_offsets joint_update_expected_nodes 1279 joint_update_expr_1279);
 [exact joint_update_node_positions|exact joint_update_node_safety|apply (List.nth_error_In joint_update_expected_nodes 824%nat); vm_compute;reflexivity| |exact S1].
 intros site. cbn [joint_update_expr_1279 eval_hfexpr_validif_policy eval_href_validif_policy]. rewrite Mode. destruct sub;reflexivity. }
 assert (H1280 : VM.find 1280 s1 = Some (Gval (Fuint 1) [::sub])).
 { eapply (reference_redirect_ground_step joint_update_node_offsets joint_update_expected_nodes 1280 joint_update_expr_1280);
 [exact joint_update_node_positions|exact joint_update_node_safety|apply (List.nth_error_In joint_update_expected_nodes 825%nat); vm_compute;reflexivity| |exact S1].
 intros site. cbn [joint_update_expr_1280 eval_hfexpr_validif_policy eval_href_validif_policy]. rewrite Mode. destruct sub;reflexivity. }
 assert (Guard : VM.find 1281 s2 = Some (Gval (Fuint 1) [::true])).
 { eapply (reference_redirect_ground_step joint_update_node_offsets joint_update_expected_nodes 1281 joint_update_expr_1281);
 [exact joint_update_node_positions|exact joint_update_node_safety|apply (List.nth_error_In joint_update_expected_nodes 826%nat); vm_compute;reflexivity| |exact S2].
 intros site. cbn [joint_update_expr_1281 eval_hfexpr_validif_policy eval_href_validif_policy]. rewrite H1279 H1280. destruct sub;reflexivity. }
 destruct (alu_selected_mux_node 1303 1281 1161 1302 invalid s2 s2 s3 32 word
   ltac:(apply (List.nth_error_In joint_update_expected_nodes 848%nat); vm_compute;reflexivity) Guard Sum Size S3) as [value [Output Adapt]].
 eapply (declared_connection_value 1229 flat_statements joint_update_connection_1154_decl joint_update_connection_1154_mid joint_update_connection_1154_tail 1154 1303 32 value);
 [exact joint_update_connection_1154_position|exact joint_update_connection_1154_split|exact joint_update_connection_1154_straight|exact joint_update_connection_1154_mid_safe|exact joint_update_connection_1154_tail_safe|exact joint_update_connection_1154_nonregister|reflexivity|exact Output|exact Adapt|exact S4].
Qed.
Theorem rf_alu_subtract_from_inputs invalid history left right :
 size left=32%nat ->size right=32%nat ->
 VM.find 1152(history 0%nat)=Some(Gval(Fuint 32)right) ->
 VM.find 1153(history 1%nat)=Some(Gval(Fuint 4)[::true;false;false;false]) ->
 VM.find 1152(history 2%nat)=Some(Gval(Fuint 32)right) ->
 VM.find 1151(history 3%nat)=Some(Gval(Fuint 32)left) ->
 (forall i,(i<5)%coq_nat ->formal_value_iter invalid flat_memories(history i)false(history i)flat_statements=Some(history(S i))) ->
 VM.find 1161(history 5%nat)=Some(Gval(Fuint 32)(dut_branch_difference left right)).
Proof.
 intros LeftSize RightSize Right0 Mode Right2 Left Steps.
 pose proof(rf_alu_negated_value invalid(history 0%nat)(history 1%nat)(history 2%nat)right Right0(Steps 0%nat ltac:(lia))(Steps 1%nat ltac:(lia)))as Neg.
 pose proof(rf_alu_select_sub invalid(history 1%nat)(history 2%nat)(history 3%nat)right Mode Right2 Neg(Steps 1%nat ltac:(lia))(Steps 2%nat ltac:(lia)))as Selected.
 pose proof(alu_address_add_history invalid(history 3%nat)(history 4%nat)(history 5%nat)left(rf_negated_word right)Left Selected(Steps 3%nat ltac:(lia))(Steps 4%nat ltac:(lia)))as Sum.
 rewrite(rf_subtract_sum left right LeftSize RightSize)in Sum;exact Sum.
Qed.
