Require Import StagedFlatObservation.
Require Import PipelinePCRelation PipelinePCReachabilityInduction ObservedAssertion43FromPCSources.
Require Import CoreSocModel ComparisonNodes FormalDeclaredWireCheck FormalAssertionDischarge
 AssertionInstances ComparisonTruth FormalObservedHistory FormalLocalHistory ExceptionPCSourceRegisters
 ObservedAssertion43FromPipeline PipelinePCPreservationReduction ReferenceRedirectSemantics.
From Coq Require Import NArith ZArith Lia.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From nbits Require Import NBits.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Firrtl_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
(* Two checker wires, certified together against the unchanged flattened model. *)
Lemma pipeline_pc_checker_wires reference : declared_wire_check flat_memories flat_statements
 (if reference then 1638 else 1476) (if reference then 6137 else 7408)
 (if reference then 1559 else 1397) (if reference then 7331 else 7751) 32 = true.
Proof. destruct reference; vm_compute; reflexivity. Qed.
Local Opaque flat_statements flat_memories generated_modules generated_top.
Lemma pipeline_pc_checker_wire reference invalid old current result bits :
 size bits = 32%nat ->
 VM.find (if reference then 7331 else 7751) old = Some (Gval (Fuint 32) bits) ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find (if reference then 1559 else 1397) result = Some (Gval (Fuint 32) bits).
Proof.
 intros Size Source Step.
 eapply declared_wire_checked_value; [exact (pipeline_pc_checker_wires reference)|exact Source| |exact Step].
 exact (reference_redirect_adapt_word bits Size).
Qed.
Theorem pipeline_pc_checker_window invalid history bits :
 (forall i, (i < 9259)%coq_nat -> formal_value_iter invalid flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 size bits = 32%nat ->
 VM.find 7751 (history 9259%nat) = Some (Gval (Fuint 32) bits) ->
 VM.find 7331 (history 9259%nat) = Some (Gval (Fuint 32) bits) ->
 comparison_inputs_agree (history 9258%nat) 1397 1559.
Proof.
 intros Steps Size DUT Ref.
 destruct (exception_pc_sources_history_stable invalid history 9259 9257 Steps ltac:(vm_compute;lia)) as [D R].
 assert (DWire : VM.find 1397 (history 9258%nat) = Some (Gval (Fuint 32) bits)).
 { eapply (pipeline_pc_checker_wire false invalid (history 9257%nat) (history 9257%nat) (history 9258%nat)); [exact Size|rewrite D;exact DUT|apply Steps;vm_compute;lia]. }
 assert (RWire : VM.find 1559 (history 9258%nat) = Some (Gval (Fuint 32) bits)).
 { eapply (pipeline_pc_checker_wire true invalid (history 9257%nat) (history 9257%nat) (history 9258%nat)); [exact Size|rewrite R;exact Ref|apply Steps;vm_compute;lia]. }
 exists 32%nat, 32%nat, bits, bits. repeat split; try assumption.
Qed.

Require Import Assertion44Enable NormalizedBit ReferenceRedirectSpine X0ConcretePositionCertificate X0ConcreteSafetyCertificate.
Definition pipeline_pc_enable (valid guard : VarOrder.T) :=
 @Eprim_binop VarOrder.T Band (@Eprim_binop VarOrder.T Band
 (@Eprim_binop VarOrder.T Band (@Econst VarOrder.T (Fuint 1) [::true])
 (@Eref VarOrder.T (@Eid VarOrder.T valid))) (@Eref VarOrder.T (@Eid VarOrder.T guard)))
 (@Econst VarOrder.T (Fuint 1) [::true]).
Lemma pipeline_pc_enabled_parts env valid guard value gv :
 VM.find valid env = Some value -> normalized_bit value ->
 VM.find guard env = Some gv -> normalized_bit gv ->
 generated_expr_true (pipeline_pc_enable valid guard) env ->
 value = Gval (Fuint 1) [::true] /\ gv = Gval (Fuint 1) [::true].
Proof.
 intros V NV G NG Enabled.
 unfold generated_expr_true, pipeline_pc_enable in Enabled.
 cbn [eval_hfexpr eval_href] in Enabled. rewrite V G in Enabled.
 destruct NV as [v| | |]; destruct NG as [g| | |]; try destruct v; try destruct g;
 vm_compute in Enabled; try discriminate Enabled; try contradiction; split; reflexivity.
Qed.
Definition pipeline_pc_guard_cast i := N.add 7596 (4 * N.of_nat i).
Definition pipeline_pc_guard_id i := N.add 7597 (4 * N.of_nat i).
Definition pipeline_pc_guard_cast_expr := @Ecast VarOrder.T AsUInt (@Eref VarOrder.T (@Eid VarOrder.T 1394)).
Definition pipeline_pc_guard_expr i := @Eprim_binop VarOrder.T (Bcomp Beq)
 (@Eref VarOrder.T (@Eid VarOrder.T (pipeline_pc_guard_cast i))) (@Econst VarOrder.T (Fuint 1) [::false]).
Definition pipeline_pc_guard_nodes : seq (VarOrder.T * hfexpr VarOrder.T) :=
 flatten (map (fun i => [::(pipeline_pc_guard_cast i,pipeline_pc_guard_cast_expr);
 (pipeline_pc_guard_id i,pipeline_pc_guard_expr i)]) (iota 0 33)).
Definition pipeline_pc_guard_offsets := 8065%nat :: 0%nat :: flatten (nseq 32 [::2%nat;0%nat]).
Local Transparent flat_statements flat_memories.
Lemma pipeline_pc_guard_positions : select_node_offsets pipeline_pc_guard_offsets flat_statements = Some pipeline_pc_guard_nodes.
Proof. vm_compute;reflexivity. Qed.
Lemma pipeline_pc_guard_safety : selected_node_safety flat_memories flat_statements pipeline_pc_guard_offsets flat_statements = true.
Proof. vm_compute;reflexivity. Qed.
Local Opaque flat_statements flat_memories.
Lemma pipeline_pc_guard_members i : (i < 33)%coq_nat ->
 List.In (pipeline_pc_guard_cast i,pipeline_pc_guard_cast_expr) pipeline_pc_guard_nodes /\
 List.In (pipeline_pc_guard_id i,pipeline_pc_guard_expr i) pipeline_pc_guard_nodes.
Proof.
 intro Bound. split.
 - apply (List.nth_error_In pipeline_pc_guard_nodes (Nat.mul 2 i)).
   do 33 (destruct i as [|i]; [vm_compute;reflexivity|]);lia.
 - apply (List.nth_error_In pipeline_pc_guard_nodes (S (Nat.mul 2 i))).
   do 33 (destruct i as [|i]; [vm_compute;reflexivity|]);lia.
Qed.
Lemma pipeline_pc_guard_after_two i invalid s0 s1 s2 bit :
 (i < 33)%coq_nat ->
 VM.find 1394 s0 = Some (Gval (Fuint 1) [::bit]) ->
 formal_value_iter invalid flat_memories s0 false s0 flat_statements = Some s1 ->
 formal_value_iter invalid flat_memories s1 false s1 flat_statements = Some s2 ->
 VM.find (pipeline_pc_guard_id i) s2 = Some (Gval (Fuint 1) [::negb bit]).
Proof.
 intros Bound Reset S1 S2.
 destruct (pipeline_pc_guard_members i Bound) as [MC MG].
 assert (Cast : VM.find (pipeline_pc_guard_cast i) s1 = Some (Gval (Fuint 1) [::bit])).
 { eapply (reference_redirect_ground_step pipeline_pc_guard_offsets pipeline_pc_guard_nodes (pipeline_pc_guard_cast i));
   [exact pipeline_pc_guard_positions|exact pipeline_pc_guard_safety|exact MC| |exact S1].
   intros site; cbn [pipeline_pc_guard_cast_expr eval_hfexpr_validif_policy eval_href_validif_policy]. rewrite Reset. destruct bit;reflexivity. }
 eapply (reference_redirect_ground_step pipeline_pc_guard_offsets pipeline_pc_guard_nodes (pipeline_pc_guard_id i));
 [exact pipeline_pc_guard_positions|exact pipeline_pc_guard_safety|exact MG| |exact S2].
 intros site; cbn [pipeline_pc_guard_expr eval_hfexpr_validif_policy eval_href_validif_policy]. rewrite Cast. destruct bit;reflexivity.
Qed.

Require Import CheckerValidBitValues FormalCheckerValidStability FormalStallHistory FormalCheckerResetConnections.
Lemma pipeline_pc_valid_history invalid history bubble reset :
 (forall i, (i < 9259)%coq_nat -> formal_value_iter invalid flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 (forall i, (i <= 9259)%coq_nat -> VM.find 1 (history i) = Some (Gval (Fuint 1) [::reset])) ->
 VM.find 7947 (history 9259%nat) = Some (Gval (Fuint 1) [::bubble]) ->
 VM.find 1395 (history 9259%nat) = Some (Gval (Fuint 1) [::negb ((bubble || reset) || reset)]).
Proof.
 intros Steps Resets Bubble.
 assert (B6 : VM.find 7947 (history 6%nat) = Some (Gval (Fuint 1) [::bubble])).
 { rewrite (flat_register_history_same invalid history 9259 7947 formal_checker_bubble_register Steps 6 ltac:(vm_compute;lia)).
   rewrite (flat_register_history_same invalid history 9259 7947 formal_checker_bubble_register Steps 9259 ltac:(vm_compute;lia)) in Bubble. exact Bubble. }
 assert (Stall : VM.find 7765 (history 6%nat) = Some (Gval (Fuint 1) [::reset])).
 { apply (stall_after_six invalid (history 0%nat) (history 1%nat) (history 2%nat) (history 3%nat)
   (history 4%nat) (history 5%nat) (history 6%nat) reset);
   [apply Resets|apply Steps|apply Steps|apply Steps|apply Steps|apply Steps|apply Steps];vm_compute;lia. }
 assert (Reset : VM.find 65 (history 6%nat) = Some (Gval (Fuint 1) [::reset])).
 { apply (reset_connection_65_transfer invalid (history 5%nat) (history 5%nat) (history 6%nat) reset).
   - apply (reset_connection_24_transfer invalid (history 4%nat) (history 4%nat) (history 5%nat) reset);
     [apply Resets|apply Steps];vm_compute;lia.
   - apply Steps;vm_compute;lia. }
 pose proof (checker_valid_bits_after_six invalid (history 6%nat) (history 7%nat) (history 8%nat)
 (history 9%nat) (history 10%nat) (history 11%nat) (history 12%nat) bubble reset reset B6 Stall Reset
 (Steps 6%nat ltac:(vm_compute;lia)) (Steps 7%nat ltac:(vm_compute;lia))
 (Steps 8%nat ltac:(vm_compute;lia)) (Steps 9%nat ltac:(vm_compute;lia))
 (Steps 10%nat ltac:(vm_compute;lia)) (Steps 11%nat ltac:(vm_compute;lia))) as Valid.
 pose proof (checker_valid_history_stable invalid history 9259 0 9247 reset Steps Resets ltac:(vm_compute;lia) ltac:(vm_compute;lia)) as Same.
 change (VM.find 1395 (history 12%nat) = VM.find 1395 (history 9259%nat)) in Same.
 rewrite <- Same. exact Valid.
Qed.
Lemma pipeline_pc_enabled_history i invalid history bubble reset :
 (i < 33)%coq_nat ->
 (forall j, (j < 9259)%coq_nat -> formal_value_iter invalid flat_memories (history j) false (history j) flat_statements = Some (history (S j))) ->
 (forall j, (j <= 9259)%coq_nat -> VM.find 1 (history j) = Some (Gval (Fuint 1) [::reset])) ->
 VM.find 7947 (history 9259%nat) = Some (Gval (Fuint 1) [::bubble]) ->
 generated_expr_true (pipeline_pc_enable 1395 (pipeline_pc_guard_id i)) (history 9259%nat) ->
 bubble = false /\ reset = false /\ VM.find 1395 (history 9259%nat) = Some (Gval (Fuint 1) [::true]).
Proof.
 intros Bound Steps Resets Bubble Enabled.
 pose proof (pipeline_pc_valid_history invalid history bubble reset Steps Resets Bubble) as Valid.
 pose proof (assertion44_checker_reset_after_three invalid (history 9254%nat) (history 9255%nat) (history 9256%nat) (history 9257%nat) reset
 (Resets 9254%nat ltac:(vm_compute;lia)) (Steps 9254%nat ltac:(vm_compute;lia))
 (Steps 9255%nat ltac:(vm_compute;lia)) (Steps 9256%nat ltac:(vm_compute;lia))) as Reset.
 pose proof (pipeline_pc_guard_after_two i invalid (history 9257%nat) (history 9258%nat) (history 9259%nat) reset Bound Reset
 (Steps 9257%nat ltac:(vm_compute;lia)) (Steps 9258%nat ltac:(vm_compute;lia))) as Guard.
 destruct (pipeline_pc_enabled_parts _ _ _ _ _ Valid (normalized_known _) Guard (normalized_known _) Enabled) as [V G].
 destruct bubble, reset; try discriminate V; try discriminate G. repeat split;exact Valid.
Qed.

Theorem pipeline_pc_enabled_observed i memory inputs k observed bubble :
 (i < 33)%coq_nat ->
 generated_observe memory inputs k = Some observed ->
 generated_legal_trace memory inputs k ->
 VM.find 7947 (top_environment observed) = Some (Gval (Fuint 1) [::bubble]) ->
 generated_expr_true (pipeline_pc_enable 1395 (pipeline_pc_guard_id i)) (top_environment observed) ->
 bubble = false /\
 VM.find 1 (top_environment observed) = Some (Gval (Fuint 1) [::false]) /\
 VM.find 1395 (top_environment observed) = Some (Gval (Fuint 1) [::true]).
Proof.
 intros Bound Observe Legal Bubble Enabled.
 destruct (observed_history memory inputs k observed Observe Legal) as [reset [history [Last [Steps Resets]]]].
 assert (BH : VM.find 7947 (history 9259%nat) = Some (Gval (Fuint 1) [::bubble])) by (rewrite Last;exact Bubble).
 assert (EH : generated_expr_true (pipeline_pc_enable 1395 (pipeline_pc_guard_id i)) (history 9259%nat)) by (rewrite Last;exact Enabled).
 destruct (pipeline_pc_enabled_history i _ history bubble reset Bound Steps Resets BH EH) as [B [R V]].
 subst reset. split;[exact B|]. split.
 - rewrite <- Last. apply Resets;vm_compute;lia.
 - rewrite <- Last;exact V.
Qed.
Theorem observed_assertion7_from_pipeline memory inputs k observed :
 generated_observe memory inputs k = Some observed ->
 generated_legal_trace memory inputs k ->
 pipeline_pc_relation (top_environment observed) ->
 generated_assert_m0_7_all observed.
Proof.
 intros Observe Legal Relation.
 destruct (observed_last_iteration memory inputs k observed Observe)
 as [committed [initial [previous [old [next [Run [Prepare [Prefix [Old [Step State]]]]]]]]]].
 assert (Top : top_environment observed = next) by (unfold top_environment;rewrite State;reflexivity).
 apply (proj2 (assertion_7_at_top observed)). rewrite State. rewrite <- Top.
 unfold generated_assert_m0_7_local. intro Enabled.
 destruct (pipeline_pc_relation_bubble _ Relation) as [bubble Bubble].
 destruct (pipeline_pc_enabled_observed 0 memory inputs k observed bubble ltac:(lia) Observe Legal Bubble Enabled) as [B Rest].
 subst bubble.
 destruct (pipeline_pc_relation_commit _ Relation Bubble) as [bits [Size [Aligned [DUT Ref]]]].
 destruct (observed_history memory inputs k observed Observe Legal) as [reset [history [Last [Steps Resets]]]].
 assert (Agree : comparison_inputs_agree (history 9258%nat) 1397 1559).
 { apply (pipeline_pc_checker_window _ history bits Steps Size);rewrite Last;assumption. }
 pose proof (Steps 9258%nat ltac:(vm_compute;lia)) as Final.
 change (formal_value_iter (formal_invalid_policy (generated_observation_input inputs k) nil) flat_memories
 (history 9258%nat) false (history 9258%nat) flat_statements = Some (history 9259%nat)) in Final.
 rewrite Last in Final.
 exact ((assertion_7_from_enabled_agreement _ _ _ _ Final (fun _ => Agree)) Enabled).
Qed.
Theorem observed_pc_assertions_from_pipeline memory inputs k observed :
 generated_observe memory inputs k = Some observed ->
 generated_legal_trace memory inputs k ->
 pipeline_pc_relation (top_environment observed) ->
 generated_assert_m0_7_all observed /\ generated_assert_m0_43_all observed.
Proof.
 intros Observe Legal Relation; split.
 - exact (observed_assertion7_from_pipeline memory inputs k observed Observe Legal Relation).
 - exact (observed_assertion43_from_pipeline memory inputs k observed Observe Legal Relation).
Qed.
Theorem pc_assertions_from_active_preservation memory inputs :
 pipeline_pc_active_preservation memory inputs ->
 forall k observed, generated_observe memory inputs k = Some observed ->
 generated_legal_trace memory inputs k ->
 generated_assert_m0_7_all observed /\ generated_assert_m0_43_all observed.
Proof.
 intros Active k observed Observe Legal.
 apply (observed_pc_assertions_from_pipeline memory inputs k observed Observe Legal).
 exact (pipeline_pc_observation_from_preservation memory inputs
 (pipeline_pc_step_from_active memory inputs Active) k observed Observe Legal).
Qed.
