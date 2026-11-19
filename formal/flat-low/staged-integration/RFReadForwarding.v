Require Import RFWriteEffect CoreSocModel ComparisonNodes ExactWordMux CommitPCAdvance SelectedNodeSafety FormalTypedNodeEquation DataAddressExpressionCertificates DataAddressPositionCertificate DataAddressSafetyCertificate.
From Coq Require Import ZArith NArith.Nnat List.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From nbits Require Import NBits.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Definition rf_write_hits (enabled : bool) (destination address : nat) :=
 enabled && (address != 0) && (address == destination).
Definition rf_forward_guard (enabled alu : bool) (destination address : nat) :=
 alu && rf_write_hits enabled destination address.
Definition rf_read_forward (bank : rf_bank) enabled alu destination address alu_data :=
 if rf_forward_guard enabled alu destination address then alu_data else bank address.
Lemma rf_apply_effect_hit reference enabled destination write_data address :
 rf_apply_effect reference (if enabled then RFWrite destination write_data else RFNoWrite) address =
 (if rf_write_hits enabled destination address then write_data else rf_apply_effect reference RFNoWrite address).
Proof.
 destruct address as [|address]; destruct enabled; unfold rf_write_hits, rf_apply_effect; cbn; reflexivity.
Qed.
(* A write effect is supplied by the actual bank update proof; it is not assumed
   that non-ALU writebacks are forwarded by the ALU-only implementation mux. *)
Theorem rf_paired_write_read_forward bank reference after enabled alu destination address alu_data write_data :
 bank address = rf_apply_effect reference RFNoWrite address ->
 after address = rf_apply_effect reference (if enabled then RFWrite destination write_data else RFNoWrite) address ->
 (alu = true -> alu_data = write_data) ->
 (alu = false -> rf_write_hits enabled destination address = true -> bank address = write_data) ->
 rf_read_forward bank enabled alu destination address alu_data = after address.
Proof.
 intros Paired Effect AluData NonAlu. rewrite Effect rf_apply_effect_hit.
 unfold rf_read_forward, rf_forward_guard.
 destruct alu; cbn.
 - destruct (rf_write_hits enabled destination address); [apply AluData;reflexivity|exact Paired].
 - destruct (rf_write_hits enabled destination address) eqn:Hit; [apply NonAlu;reflexivity || assumption|exact Paired].
Qed.
Corollary rf_paired_write_read_forward_alu bank reference after enabled alu destination address alu_data write_data :
 bank address = rf_apply_effect reference RFNoWrite address ->
 after address = rf_apply_effect reference (if enabled then RFWrite destination write_data else RFNoWrite) address ->
 (alu = true -> alu_data = write_data) ->
 (rf_write_hits enabled destination address = true -> alu = true) ->
 rf_read_forward bank enabled alu destination address alu_data = after address.
Proof.
 intros Paired Effect Data Coverage. apply (rf_paired_write_read_forward bank reference after enabled alu destination address alu_data write_data Paired Effect Data).
 intros False Hit. rewrite (Coverage Hit) in False. discriminate False.
Qed.
Lemma rf_forward_zero bank enabled alu destination alu_data :
 rf_read_forward bank enabled alu destination 0 alu_data = bank 0.
Proof. unfold rf_read_forward, rf_forward_guard, rf_write_hits. destruct enabled,alu;reflexivity. Qed.
Definition rf_forward_node (second : bool) : VarOrder.T := if second then 7819 else 7816.
Definition rf_forward_condition (second : bool) : VarOrder.T := if second then 7818 else 7815.
Definition rf_forward_raw (second : bool) : VarOrder.T := if second then 783 else 782.
Definition rf_forward_expression (second : bool) :=
 @Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T (rf_forward_condition second)))
 (@Eref VarOrder.T (@Eid VarOrder.T 7752)) (@Eref VarOrder.T (@Eid VarOrder.T (rf_forward_raw second))).
Lemma rf_forward_members second :
 List.In (rf_forward_node second,rf_forward_expression second) data_address_expected_nodes.
Proof.
 destruct second.
 - apply (List.nth_error_In data_address_expected_nodes 141%nat). vm_compute;reflexivity.
 - apply (List.nth_error_In data_address_expected_nodes 138%nat). vm_compute;reflexivity.
Qed.
Local Opaque flat_statements flat_memories generated_modules generated_top.
Theorem rf_actual_forward_mux second invalid old current result bit alu_data raw :
 size alu_data = 32%nat -> size raw = 32%nat ->
 VM.find (rf_forward_condition second) old = Some (Gval (Fuint 1) [::bit]) ->
 VM.find 7752 old = Some (Gval (Fuint 32) alu_data) ->
 VM.find (rf_forward_raw second) old = Some (Gval (Fuint 32) raw) ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find (rf_forward_node second) result = Some (Gval (Fuint 32) (if bit then alu_data else raw)).
Proof.
 intros AluSize RawSize Condition Alu Raw Step.
 destruct (selected_node_safe_position flat_memories flat_statements data_address_node_offsets flat_statements data_address_expected_nodes
 (rf_forward_node second) (rf_forward_expression second) data_address_actual_node_expressions data_address_actual_nodes_safe (rf_forward_members second))
 as [count [tail [Position [Safe Nonreg]]]].
 assert (Eval : eval_hfexpr_with_memory flat_memories (rf_forward_expression second) old old = Some (Gval (Fuint 32) (if bit then alu_data else raw))).
 { unfold rf_forward_expression.
 pose proof (exact_word_mux flat_memories old (rf_forward_condition second) 7752 (rf_forward_raw second) bit alu_data raw Condition Alu Raw) as E.
 rewrite (mux_word_selected_sized bit alu_data raw ltac:(destruct bit;assumption)) in E. exact E. }
 eapply formal_combinational_known_node; [exact Position|exact Safe|exact Nonreg|exact Eval|reflexivity|exact Step].
Qed.
Theorem rf_actual_paired_read_forward second invalid old current result bank reference after enabled alu destination address alu_data write_data :
 size alu_data = 32%nat -> size (bank address) = 32%nat ->
 VM.find (rf_forward_condition second) old = Some (Gval (Fuint 1) [::rf_forward_guard enabled alu destination address]) ->
 VM.find 7752 old = Some (Gval (Fuint 32) alu_data) ->
 VM.find (rf_forward_raw second) old = Some (Gval (Fuint 32) (bank address)) ->
 bank address = rf_apply_effect reference RFNoWrite address ->
 after address = rf_apply_effect reference (if enabled then RFWrite destination write_data else RFNoWrite) address ->
 (alu = true -> alu_data = write_data) ->
 (alu = false -> rf_write_hits enabled destination address = true -> bank address = write_data) ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find (rf_forward_node second) result = Some (Gval (Fuint 32) (after address)).
Proof.
 intros Size RawSize Guard Data Raw Paired Effect AluData NonAlu Step.
 pose proof (rf_actual_forward_mux second invalid old current result _ alu_data (bank address) Size RawSize Guard Data Raw Step) as Value.
 change (VM.find (rf_forward_node second) result = Some (Gval (Fuint 32) (rf_read_forward bank enabled alu destination address alu_data))) in Value.
 rewrite (rf_paired_write_read_forward bank reference after enabled alu destination address alu_data write_data Paired Effect AluData NonAlu) in Value.
 exact Value.
Qed.

Definition rf_guard_nodes (second : bool) : seq (VarOrder.T * hfexpr VarOrder.T) :=
 if second then [::(7810,address_expr_7810);(7811,address_expr_7811);(7812,address_expr_7812);(7813,address_expr_7813);(7817,address_expr_7817);(7818,address_expr_7818)]
 else [::(7806,address_expr_7806);(7807,address_expr_7807);(7808,address_expr_7808);(7809,address_expr_7809);(7814,address_expr_7814);(7815,address_expr_7815)].
Definition rf_guard_entry second stage := nth (0,@Econst VarOrder.T (Fuint 1) [::false]) (rf_guard_nodes second) stage.
Lemma rf_guard_members second stage : (stage < 6)%nat ->
 List.In (rf_guard_entry second stage) data_address_expected_nodes.
Proof.
 destruct second; destruct stage as [|[|[|[|[|[|stage]]]]]]; intro Bound; try discriminate Bound.
 - apply (List.nth_error_In data_address_expected_nodes 132%nat). vm_compute;reflexivity.
 - apply (List.nth_error_In data_address_expected_nodes 133%nat). vm_compute;reflexivity.
 - apply (List.nth_error_In data_address_expected_nodes 134%nat). vm_compute;reflexivity.
 - apply (List.nth_error_In data_address_expected_nodes 135%nat). vm_compute;reflexivity.
 - apply (List.nth_error_In data_address_expected_nodes 139%nat). vm_compute;reflexivity.
 - apply (List.nth_error_In data_address_expected_nodes 140%nat). vm_compute;reflexivity.
 - apply (List.nth_error_In data_address_expected_nodes 128%nat). vm_compute;reflexivity.
 - apply (List.nth_error_In data_address_expected_nodes 129%nat). vm_compute;reflexivity.
 - apply (List.nth_error_In data_address_expected_nodes 130%nat). vm_compute;reflexivity.
 - apply (List.nth_error_In data_address_expected_nodes 131%nat). vm_compute;reflexivity.
 - apply (List.nth_error_In data_address_expected_nodes 136%nat). vm_compute;reflexivity.
 - apply (List.nth_error_In data_address_expected_nodes 137%nat). vm_compute;reflexivity.
Qed.
Lemma rf_guard_step second stage invalid old current result bit :
 (stage < 6)%nat ->
 eval_hfexpr_with_memory flat_memories (snd (rf_guard_entry second stage)) old old = Some (Gval (Fuint 1) [::bit]) ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find (fst (rf_guard_entry second stage)) result = Some (Gval (Fuint 1) [::bit]).
Proof.
 intros Bound Eval Step.
 pose proof (rf_guard_members second stage Bound) as Member.
 assert (Policy : forall site,
 eval_hfexpr_validif_policy (isolated_validif_policy invalid) site flat_memories (snd (rf_guard_entry second stage)) old old =
 eval_hfexpr_with_memory flat_memories (snd (rf_guard_entry second stage)) old old).
 { destruct second; destruct stage as [|[|[|[|[|[|stage]]]]]]; try discriminate Bound; intro site;reflexivity. }
 destruct (rf_guard_entry second stage) as [node expression] eqn:Entry. cbn [fst snd] in Eval, Policy |- *.
 destruct (selected_node_safe_position flat_memories flat_statements data_address_node_offsets flat_statements data_address_expected_nodes node expression data_address_actual_node_expressions data_address_actual_nodes_safe Member)
 as [count [tail [Position [Safe Nonreg]]]].
 eapply (formal_combinational_known_node count flat_statements tail node expression 1 (Gval (Fuint 1) [::bit]) invalid flat_memories old current result); [exact Position|exact Safe|exact Nonreg|rewrite Policy;exact Eval|reflexivity|exact Step].
Qed.
Definition rf_source_address (second : bool) : VarOrder.T := if second then 7804 else 7803.
Theorem rf_actual_forward_guard_after_four second invalid s0 s1 s2 s3 s4 read_address destination enabled low high :
 VM.find (rf_source_address second) s0 = Some (Gval (Fuint 5) read_address) ->
 VM.find (rf_source_address second) s1 = Some (Gval (Fuint 5) read_address) ->
 VM.find 7805 s1 = Some (Gval (Fuint 5) destination) ->
 VM.find 7757 s1 = Some (Gval (Fuint 1) [::enabled]) ->
 VM.find 7756 s2 = Some (Gval (Fuint 2) [::low;high]) ->
 formal_value_iter invalid flat_memories s0 false s0 flat_statements = Some s1 ->
 formal_value_iter invalid flat_memories s1 false s1 flat_statements = Some s2 ->
 formal_value_iter invalid flat_memories s2 false s2 flat_statements = Some s3 ->
 formal_value_iter invalid flat_memories s3 false s3 flat_statements = Some s4 ->
 VM.find (rf_forward_condition second) s4 = Some (Gval (Fuint 1)
 [::(~~low && ~~high) && ((enabled && foldr orb false read_address) && (to_N read_address == to_N destination))]).
Proof.
 intros Address0 Address1 Destination Enabled Mode S1 S2 S3 S4.
 assert (Nonzero : VM.find (fst (rf_guard_entry second 0)) s1 = Some (Gval (Fuint 1) [::foldr orb false read_address])).
 { apply (rf_guard_step second 0 invalid s0 s0 s1); [reflexivity| |exact S1].
 destruct second; cbn [rf_guard_entry rf_guard_nodes snd nth address_expr_7810 address_expr_7806 eval_hfexpr_with_memory eval_href_with_memory rf_source_address] in *; rewrite Address0;reflexivity. }
 assert (Write : VM.find (fst (rf_guard_entry second 1)) s2 = Some (Gval (Fuint 1) [::enabled && foldr orb false read_address])).
 { apply (rf_guard_step second 1 invalid s1 s1 s2); [reflexivity| |exact S2].
 destruct second; cbn [rf_guard_entry rf_guard_nodes fst snd nth address_expr_7811 address_expr_7807 eval_hfexpr_with_memory eval_href_with_memory] in *; rewrite Enabled Nonzero; destruct enabled, (foldr orb false read_address);reflexivity. }
 assert (Equal : VM.find (fst (rf_guard_entry second 2)) s2 = Some (Gval (Fuint 1) [::to_N read_address == to_N destination])).
 { apply (rf_guard_step second 2 invalid s1 s1 s2); [reflexivity| |exact S2].
 destruct second; cbn [rf_guard_entry rf_guard_nodes fst snd nth address_expr_7812 address_expr_7808 eval_hfexpr_with_memory eval_href_with_memory rf_source_address] in *; rewrite Address1 Destination;reflexivity. }
 assert (Hit : VM.find (fst (rf_guard_entry second 3)) s3 = Some (Gval (Fuint 1) [::(enabled && foldr orb false read_address) && (to_N read_address == to_N destination)])).
 { apply (rf_guard_step second 3 invalid s2 s2 s3); [reflexivity| |exact S3].
 destruct second; cbn [rf_guard_entry rf_guard_nodes fst snd nth address_expr_7813 address_expr_7809 eval_hfexpr_with_memory eval_href_with_memory] in *; rewrite Write Equal; destruct (enabled && foldr orb false read_address), (to_N read_address == to_N destination);reflexivity. }
 assert (Alu : VM.find (fst (rf_guard_entry second 4)) s3 = Some (Gval (Fuint 1) [::~~low && ~~high])).
 { apply (rf_guard_step second 4 invalid s2 s2 s3); [reflexivity| |exact S3].
 destruct second; cbn [rf_guard_entry rf_guard_nodes fst snd nth address_expr_7817 address_expr_7814 eval_hfexpr_with_memory eval_href_with_memory] in *; rewrite Mode; destruct low,high;reflexivity. }
 assert (Result : VM.find (fst (rf_guard_entry second 5)) s4 = Some (Gval (Fuint 1) [::(~~low && ~~high) && ((enabled && foldr orb false read_address) && (to_N read_address == to_N destination))])).
 {
 apply (rf_guard_step second 5 invalid s3 s3 s4); [reflexivity| |exact S4].
 destruct second; cbn [rf_guard_entry rf_guard_nodes fst snd nth address_expr_7818 address_expr_7815 eval_hfexpr_with_memory eval_href_with_memory] in *; rewrite Alu Hit; destruct (~~low && ~~high), ((enabled && foldr orb false read_address) && (to_N read_address == to_N destination));reflexivity.
 } destruct second;exact Result.
Qed.
Lemma rf_address_nonzero word : foldr orb false word = (to_nat word != 0%nat).
Proof.
 induction word as [|bit tail IH]; [reflexivity|].
 rewrite to_nat_cons. cbn [foldr].
 destruct bit; destruct (to_nat tail) eqn:E; rewrite IH;reflexivity.
Qed.
Lemma rf_address_equal left right :
 (to_N left == to_N right) = (to_nat left == to_nat right).
Proof.
 apply/idP/idP; move/eqP => Equal; apply/eqP.
 - apply Nat2N.inj. rewrite <- !to_N_nat. exact Equal.
 - rewrite !to_N_nat Equal. reflexivity.
Qed.
Theorem rf_actual_forward_guard_effect second invalid s0 s1 s2 s3 s4 read_address destination enabled low high :
 VM.find (rf_source_address second) s0 = Some (Gval (Fuint 5) read_address) ->
 VM.find (rf_source_address second) s1 = Some (Gval (Fuint 5) read_address) ->
 VM.find 7805 s1 = Some (Gval (Fuint 5) destination) ->
 VM.find 7757 s1 = Some (Gval (Fuint 1) [::enabled]) ->
 VM.find 7756 s2 = Some (Gval (Fuint 2) [::low;high]) ->
 formal_value_iter invalid flat_memories s0 false s0 flat_statements = Some s1 ->
 formal_value_iter invalid flat_memories s1 false s1 flat_statements = Some s2 ->
 formal_value_iter invalid flat_memories s2 false s2 flat_statements = Some s3 ->
 formal_value_iter invalid flat_memories s3 false s3 flat_statements = Some s4 ->
 VM.find (rf_forward_condition second) s4 = Some (Gval (Fuint 1)
 [::rf_forward_guard enabled (~~low && ~~high) (to_nat destination) (to_nat read_address)]).
Proof.
 intros A0 A1 Destination Enabled Mode S1 S2 S3 S4.
 pose proof (rf_actual_forward_guard_after_four second invalid s0 s1 s2 s3 s4 read_address destination enabled low high A0 A1 Destination Enabled Mode S1 S2 S3 S4) as Guard.
 rewrite rf_address_nonzero rf_address_equal in Guard. exact Guard.
Qed.
Theorem rf_actual_forwarding_reads_written_bank second invalid s0 s1 s2 s3 s4 s5 bank reference read_address destination enabled low high alu_data write_data :
 VM.find (rf_source_address second) s0 = Some (Gval (Fuint 5) read_address) ->
 VM.find (rf_source_address second) s1 = Some (Gval (Fuint 5) read_address) ->
 VM.find 7805 s1 = Some (Gval (Fuint 5) destination) ->
 VM.find 7757 s1 = Some (Gval (Fuint 1) [::enabled]) ->
 VM.find 7756 s2 = Some (Gval (Fuint 2) [::low;high]) ->
 size alu_data = 32%nat -> size (bank (to_nat read_address)) = 32%nat ->
 VM.find 7752 s4 = Some (Gval (Fuint 32) alu_data) ->
 VM.find (rf_forward_raw second) s4 = Some (Gval (Fuint 32) (bank (to_nat read_address))) ->
 bank (to_nat read_address) = rf_apply_effect reference RFNoWrite (to_nat read_address) ->
 ((~~low && ~~high) = true -> alu_data = write_data) ->
 ((~~low && ~~high) = false -> rf_write_hits enabled (to_nat destination) (to_nat read_address) = true -> bank (to_nat read_address) = write_data) ->
 formal_value_iter invalid flat_memories s0 false s0 flat_statements = Some s1 ->
 formal_value_iter invalid flat_memories s1 false s1 flat_statements = Some s2 ->
 formal_value_iter invalid flat_memories s2 false s2 flat_statements = Some s3 ->
 formal_value_iter invalid flat_memories s3 false s3 flat_statements = Some s4 ->
 formal_value_iter invalid flat_memories s4 false s4 flat_statements = Some s5 ->
 VM.find (rf_forward_node second) s5 = Some (Gval (Fuint 32)
 (rf_apply_effect reference (if enabled then RFWrite (to_nat destination) write_data else RFNoWrite) (to_nat read_address))).
Proof.
 intros A0 A1 Destination Enabled Mode Size RawSize Data Raw Paired AluData NonAlu S1 S2 S3 S4 S5.
 pose proof (rf_actual_forward_guard_effect second invalid s0 s1 s2 s3 s4 read_address destination enabled low high A0 A1 Destination Enabled Mode S1 S2 S3 S4) as Guard.
 exact (rf_actual_paired_read_forward second invalid s4 s4 s5 bank reference
 (rf_apply_effect reference (if enabled then RFWrite (to_nat destination) write_data else RFNoWrite))
 enabled (~~low && ~~high) (to_nat destination) (to_nat read_address) alu_data write_data
 Size RawSize Guard Data Raw Paired (Logic.eq_refl _) AluData NonAlu S5).
Qed.
