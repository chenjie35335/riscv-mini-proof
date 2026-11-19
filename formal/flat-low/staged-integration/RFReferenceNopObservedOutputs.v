Require Import CoreSocModel ComparisonNodes RFReferenceNopCycle RFReferenceNopHistory RFWriteEffect FormalDeclaredWireCheck FormalInstructionResetConstants.
From Coq Require Import ZArith List Lia.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From nbits Require Import NBits.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Local Opaque flat_statements flat_memories generated_modules generated_top.
Definition rf_reference_output_position (index:nat) : nat := nth 0%nat [::1676%nat;1677%nat;1678%nat;1679%nat;1680%nat;1681%nat;1682%nat;1683%nat;1684%nat;1685%nat;1686%nat;1687%nat;1688%nat;1689%nat;1690%nat;1691%nat;1692%nat;1693%nat;1694%nat;1695%nat;1696%nat;1697%nat;1698%nat;1699%nat;1700%nat;1701%nat;1702%nat;1703%nat;1704%nat;1705%nat;1706%nat;1707%nat] index.
Definition rf_reference_output_distance (index:nat) : nat := nth 0%nat [::6137%nat;6137%nat;6137%nat;6137%nat;6137%nat;6137%nat;6137%nat;6137%nat;6137%nat;6137%nat;6137%nat;6137%nat;6137%nat;6137%nat;6137%nat;6137%nat;6137%nat;6137%nat;6137%nat;6137%nat;6137%nat;6137%nat;6137%nat;6137%nat;6137%nat;6137%nat;6137%nat;6137%nat;6137%nat;6137%nat;6137%nat;6137%nat] index.
Lemma rf_reference_output_certificate (index:nat) : (index < 32)%coq_nat ->
 declared_wire_check flat_memories flat_statements (rf_reference_output_position index) (rf_reference_output_distance index)
 (N.of_nat (Nat.add 1597 index)) (N.of_nat (Nat.add 1787 index)) 32 = true.
Proof. intros Bound. do 32 (destruct index as [|index]; [vm_compute;reflexivity|]). lia. Qed.
Theorem rf_reference_output_step (index:nat) invalid old current result word :
 (index < 32)%coq_nat -> size word = 32%nat ->
 VM.find (N.of_nat (Nat.add 1787 index)) old = Some (Gval (Fuint 32) word) ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find (N.of_nat (Nat.add 1597 index)) result = Some (Gval (Fuint 32) word).
Proof.
 intros Bound Size Source Step.
 eapply (declared_wire_checked_value flat_memories flat_statements (rf_reference_output_position index) (rf_reference_output_distance index)
 (N.of_nat (Nat.add 1597 index)) (N.of_nat (Nat.add 1787 index)) 32);
 [apply rf_reference_output_certificate;exact Bound|exact Source| |exact Step].
 change (Some (Gval (Fuint 32%nat) (zext_to 32%nat (take 32%nat word))) = Some (Gval (Fuint 32%nat) word)).
 rewrite -Size take_size. unfold zext_to,zext. rewrite subnn cats0. reflexivity.
Qed.
Theorem rf_reference_nop_fullhistory_outputs invalid history bank :
 rf_reference_bank_at (history 0%nat) bank -> bank 0%nat = nseq 32 false ->
 VM.find 7750 (history 0%nat) = Some (Gval (Fuint 32) instruction_nop) ->
 (forall time, (time < 9259)%coq_nat -> formal_value_iter invalid flat_memories (history time) false (history time) flat_statements = Some (history (S time))) ->
 (forall time, (time <= 9259)%coq_nat -> VM.find 1 (history time) = Some (Gval (Fuint 1) [::false])) ->
 VM.find 7947 (history 9259%nat) = Some (Gval (Fuint 1) [::false]) ->
 forall index, (index < 32)%coq_nat -> VM.find (N.of_nat (Nat.add 1597 index)) (history 9259%nat) = Some (Gval (Fuint 32) (bank index)).
Proof.
 intros Bank Zero Instruction Steps Resets Bubble index Index.
 destruct (Bank index Index) as [Size _].
 eapply (rf_reference_output_step index invalid (history 9258%nat) (history 9258%nat) (history 9259%nat) (bank index));
 [exact Index|exact Size| |apply Steps;vm_compute;lia].
 eapply (rf_reference_nop_from_writeback_sources invalid history 9259 12 bank Bank Zero Instruction
 (rf_reference_nop_checker_enabled invalid history Steps Resets Bubble) Steps 9258 ltac:(vm_compute;lia));exact Index.
Qed.
(* Additional semantic composition. *)
Require Import RFArchitecturalRelation FlatRegFileX0 RFPreviewEffect RFArchitecturalNormalRelation FormalSuccessfulNodeEvaluation FormalTypedNodeEquation SelectedNodeSafety UIntMuxResultType FormalX0WriteDataShape FormalX0SelectedType.
Theorem rf_nop_preview_nonzero_step invalid s0 s1 s2 (index:nat) word data :
 (S index < 32)%coq_nat -> size word = 32%nat ->
 VM.find (N.of_nat (851+S index)%nat) s0 = Some (Gval (Fuint 32) word) ->
 VM.find (N.of_nat (851+S index)%nat) s1 = Some (Gval (Fuint 32) word) ->
 VM.find 988 s0 = Some data -> type_of_val data = Gtyp (Fuint 32) ->
 VM.find 954 s1 = Some (Gval (Fuint 1) [::false]) ->
 formal_value_iter invalid flat_memories s0 false s0 flat_statements = Some s1 ->
 formal_value_iter invalid flat_memories s1 false s1 flat_statements = Some s2 ->
 VM.find (N.of_nat (1053+S index)%nat) s2 = Some (Gval (Fuint 32) word).
Proof.
 intros Bound Size Old0 Old1 Data Typed Gate S1 S2.
 destruct (selected_node_safe_position flat_memories flat_statements rf_preview_effect_offsets flat_statements rf_preview_effect_nodes _ _ rf_preview_effect_positions rf_preview_effect_safety (rf_preview_select_member (S index) Bound)) as [count [tail [Position [Safe Nonreg]]]].
 destruct (formal_successful_node_evaluation count flat_statements tail _ _ invalid flat_memories s0 false s0 s1 Position S1) as [selected Eval]. rewrite add0n in Eval.
 change (eval_hfexpr_with_memory flat_memories (rf_preview_select_expr (S index)) s0 s0 = Some selected) in Eval.
 assert (SelectedType : type_of_val selected = Gtyp (Fuint 32)).
 { unfold rf_preview_select_expr,rf_preview_old_expr in Eval. eapply uint_mux_result_type;[exact Data|exact Typed|exact Old0|reflexivity|exact Eval]. }
 assert (Selected : VM.find (N.of_nat (989+S index)%nat) s1 = Some selected).
 { eapply formal_combinational_known_node;[exact Position|exact Safe|exact Nonreg|exact Eval|exact SelectedType|exact S1]. }
 destruct (selected_node_safe_position flat_memories flat_statements rf_preview_effect_offsets flat_statements rf_preview_effect_nodes _ _ rf_preview_effect_positions rf_preview_effect_safety (rf_preview_output_member (S index) Bound)) as [count2 [tail2 [Position2 [Safe2 Nonreg2]]]].
 eapply formal_combinational_known_node;[exact Position2|exact Safe2|exact Nonreg2| |reflexivity|exact S2].
 change (eval_hfexpr_with_memory flat_memories (rf_preview_output_expr (S index)) s1 s1 = Some (Gval (Fuint 32) word)).
 exact (rf_dut_disabled_mux_eval flat_memories s1 _ _ selected word Gate Selected SelectedType Old1 Size).
Qed.
Lemma rf_nop_preview_zero_step invalid old result selected :
 VM.find 989 old = Some selected -> type_of_val selected = Gtyp (Fuint 32) ->
 VM.find 954 old = Some (Gval (Fuint 1) [::false]) ->
 formal_value_iter invalid flat_memories old false old flat_statements = Some result ->
 VM.find 1053 result = Some (Gval (Fuint 32) (nseq 32 false)).
Proof.
 intros Selected Typed Gate Step.
 destruct (selected_node_safe_position flat_memories flat_statements rf_preview_effect_offsets flat_statements rf_preview_effect_nodes _ _ rf_preview_effect_positions rf_preview_effect_safety (rf_preview_output_member 0 ltac:(lia))) as [count [tail [Position [Safe Nonreg]]]].
 eapply formal_combinational_known_node;[exact Position|exact Safe|exact Nonreg| |reflexivity|exact Step].
 change (eval_hfexpr_with_memory flat_memories (rf_preview_output_expr 0) old old = Some (Gval (Fuint 32) (nseq 32 false))).
 cbn [rf_preview_output_expr rf_preview_old_expr eval_hfexpr_with_memory eval_href_with_memory]. rewrite Gate.
 change (is_zero [::false]) with true. cbn. unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite Selected. cbn [option_map]. rewrite Typed. reflexivity.
Qed.
Theorem rf_nop_preview_after_four invalid s0 s1 s2 s3 s4 bank :
 rf_dut_bank_at s0 bank -> bank 0%nat = nseq 32 false -> VM.find 954 s3 = Some (Gval (Fuint 1) [::false]) ->
 formal_value_iter invalid flat_memories s0 false s0 flat_statements = Some s1 ->
 formal_value_iter invalid flat_memories s1 false s1 flat_statements = Some s2 ->
 formal_value_iter invalid flat_memories s2 false s2 flat_statements = Some s3 ->
 formal_value_iter invalid flat_memories s3 false s3 flat_statements = Some s4 ->
 forall index, (index < 32)%coq_nat -> VM.find (N.of_nat (1053+index)%nat) s4 = Some (Gval (Fuint 32) (bank index)).
Proof.
 intros Bank Zero Gate S1 S2 S3 S4 index Bound.
 destruct index as [|index].
 - rewrite Zero. destruct (x0_selected_type_after_three invalid s0 s1 s2 s3 S1 S2 S3) as [value [Value Typed]].
   exact (rf_nop_preview_zero_step invalid s3 s4 value Value Typed Gate S4).
 - pose proof (rf_dut_bank_comb_hold invalid s0 s0 s1 bank Bank S1) as Bank1.
   pose proof (rf_dut_bank_comb_hold invalid s1 s1 s2 bank Bank1 S2) as Bank2.
   pose proof (rf_dut_bank_comb_hold invalid s2 s2 s3 bank Bank2 S3) as Bank3.
   destruct (x0_write_data_typed_after_two invalid s0 s1 s2 S1 S2) as [data [Data Typed]].
   exact (rf_nop_preview_nonzero_step invalid s2 s3 s4 index (bank (S index)) data Bound (proj1 (Bank _ Bound)) (proj2 (Bank2 _ Bound)) (proj2 (Bank3 _ Bound)) Data Typed Gate S3 S4).
Qed.
Require Import FormalRFDestination FormalRFEnableShape FormalRFWriteEnable RFReferenceNopInputs JointUpdateBoundaryHistory RFDutOutputWires.
Lemma rf_nop_gate_history invalid history (limit:nat) :
 VM.find 7750 (history 0%nat) = Some (Gval (Fuint 32) instruction_nop) ->
 (forall time, (time < limit)%coq_nat -> formal_value_iter invalid flat_memories (history time) false (history time) flat_statements = Some (history (S time))) ->
 forall time, ((4 <= time)%coq_nat /\ (time <= limit)%coq_nat) ->
 VM.find 954 (history time) = Some (Gval (Fuint 1) [::false]).
Proof.
 intros Initial Steps time Bounds. do 4 (destruct time as [|time];[lia|]).
 assert (Instruction : VM.find 7750 (history time) = Some (Gval (Fuint 32) instruction_nop)).
 { rewrite (joint_update_register_history_same invalid history limit 7750 32 rf_reference_input_register_member Steps time ltac:(lia)). exact Initial. }
 pose proof (rf_destination_port_after_two invalid (history time) (history (S time)) (history (S (S time))) instruction_nop (Logic.eq_refl _) Instruction (Steps time ltac:(lia)) (Steps (S time) ltac:(lia))) as RD.
 pose proof (rf_address_nonzero_node invalid (history (S (S time))) (history (S (S time))) (history (S (S (S time)))) _ RD (Steps (S (S time)) ltac:(lia))) as Reduction.
 destruct (rf_input_enable_normalized invalid (history (S (S time))) (history (S (S time))) (history (S (S (S time)))) (Steps (S (S time)) ltac:(lia))) as [value [Value Normal]].
 exact (rf_zero_address_disables_write invalid _ _ _ value Value Normal Reduction (Steps (S (S (S time))) ltac:(lia))).
Qed.
Theorem rf_dut_nop_fullhistory_outputs invalid history bank :
 rf_dut_bank_at (history 0%nat) bank -> bank 0%nat = nseq 32 false ->
 VM.find 7750 (history 0%nat) = Some (Gval (Fuint 32) instruction_nop) ->
 (forall time, (time < 9259)%coq_nat -> formal_value_iter invalid flat_memories (history time) false (history time) flat_statements = Some (history (S time))) ->
 forall index, (index < 32)%coq_nat -> VM.find (N.of_nat (Nat.add 1399 index)) (history 9259%nat) = Some (Gval (Fuint 32) (bank index)).
Proof.
 intros Bank Zero Instruction Steps index Index.
 assert (Preview : VM.find (N.of_nat (1053+index)%nat) (history 9254%nat) = Some (Gval (Fuint 32) (bank index))).
 { eapply (rf_nop_preview_after_four invalid (history 9250%nat) (history 9251%nat) (history 9252%nat) (history 9253%nat) (history 9254%nat) bank);
   [exact (rf_dut_bank_history_hold invalid history 9259 bank Bank Steps 9250 ltac:(vm_compute;lia))|exact Zero| |apply Steps;vm_compute;lia|apply Steps;vm_compute;lia|apply Steps;vm_compute;lia|apply Steps;vm_compute;lia|exact Index].
   exact (rf_nop_gate_history invalid history 9259 Instruction Steps 9253 ltac:(vm_compute;lia)). }
 eapply (rf_dut_output_wires index invalid (history 9254%nat) (history 9255%nat) (history 9256%nat) (history 9257%nat) (history 9258%nat) (history 9259%nat) (bank index));
 [exact Index|exact (proj1 (Bank index Index))|exact Preview|apply Steps;vm_compute;lia|apply Steps;vm_compute;lia|apply Steps;vm_compute;lia|apply Steps;vm_compute;lia|apply Steps;vm_compute;lia].
Qed.
Theorem rf_nop_fullhistory_comparison_outputs invalid history :
 rf_architectural_relation (history 0%nat) -> VM.find 851 (history 0%nat) = Some rf_zero32 ->
 VM.find 7750 (history 0%nat) = Some (Gval (Fuint 32) instruction_nop) ->
 (forall time, (time < 9259)%coq_nat -> formal_value_iter invalid flat_memories (history time) false (history time) flat_statements = Some (history (S time))) ->
 (forall time, (time <= 9259)%coq_nat -> VM.find 1 (history time) = Some (Gval (Fuint 1) [::false])) ->
 VM.find 7947 (history 9259%nat) = Some (Gval (Fuint 1) [::false]) ->
 forall index, (index < 32)%coq_nat ->
 VM.find (N.of_nat (Nat.add 1399 index)) (history 9259%nat) = VM.find (N.of_nat (Nat.add 1597 index)) (history 9259%nat).
Proof.
 intros Relation X0 Instruction Steps Resets Bubble index Index.
 destruct (rf_architectural_relation_banks _ Relation) as [Dut Ref].
 assert (Zero : rf_architectural_bank (history 0%nat) 0%nat = nseq 32 false).
 { unfold rf_architectural_bank. change (match VM.find 851 (history 0%nat) with Some (Gval _ word) => word | _ => nseq 32 false end = nseq 32 false). rewrite X0. reflexivity. }
 rewrite (rf_dut_nop_fullhistory_outputs invalid history _ Dut Zero Instruction Steps index Index).
 rewrite (rf_reference_nop_fullhistory_outputs invalid history _ Ref Zero Instruction Steps Resets Bubble index Index). reflexivity.
Qed.
Require Import ObservedLegalNoTrap FormalLocalHistory FormalResetPreparation FormalInstructionResetCycle StagedObservedRegister StagedCircuitRegisterHold.
Theorem rf_architectural_nop_observed_outputs memory inputs k committed old observed :
 generated_run memory inputs k = Some committed -> SVM.find nil committed = Some old ->
 rf_architectural_relation old -> VM.find 7750 old = Some (Gval (Fuint 32) instruction_nop) ->
 generated_observe memory inputs k = Some observed -> generated_legal_trace memory inputs k ->
 VM.find 1 (formal_external_inputs (generated_observation_input inputs k)) = Some (Gval (Fuint 1) [::false]) ->
 VM.find 7947 (top_environment observed) = Some (Gval (Fuint 1) [::false]) ->
 forall index, (index < 32)%coq_nat ->
 VM.find (N.of_nat (Nat.add 1399 index)) (top_environment observed) = VM.find (N.of_nat (Nat.add 1597 index)) (top_environment observed).
Proof.
 intros Run Old Relation Instruction Observe Legal Reset Bubble index Index.
 destruct (observed_legal_no_trap_history memory inputs k observed Observe Legal Reset)
 as [previous [initial [history [Previous [Prepare [First [Last [Steps NoTrap]]]]]]]].
 rewrite Run in Previous. inversion Previous;subst previous.
 destruct (rf_storage_x0_reachable memory inputs k committed Run Legal) as [xenv [Xenv X0]].
 rewrite Old in Xenv. inversion Xenv;subst xenv.
 destruct (rf_architectural_relation_banks old Relation) as [Dut Ref].
 pose proof (rf_dut_bank_prepared committed old _ initial _ Old Dut Prepare) as Dut0.
 pose proof (rf_reference_bank_prepared committed old _ initial _ Old Ref Prepare) as Ref0.
 assert (Zero : rf_architectural_bank old 0%nat = nseq 32 false).
 { unfold rf_architectural_bank. change (match VM.find 851 old with Some (Gval _ word) => word | _ => nseq 32 false end = nseq 32 false). rewrite X0. reflexivity. }
 assert (Instruction0 : VM.find 7750 (history 0%nat) = Some (Gval (Fuint 32) instruction_nop)).
 { destruct (instruction_register_shape 7750 ltac:(vm_compute;reflexivity)) as [Safe Present].
   pose proof (staged_prepared_register_copies committed old _ initial 7750 (Logic.eq_refl _) (Logic.eq_refl _) Safe Present Old Prepare) as Copy.
   rewrite Instruction in Copy. rewrite First. unfold staged_register_lookup in Copy. unfold top_environment.
   destruct (SVM.find nil initial);[exact Copy|discriminate Copy]. }
 destruct (top_reset_prepared (Some committed) _ initial _ Reset Prepare) as [env [Env InitialReset]].
 assert (Reset0 : VM.find 1 (history 0%nat) = Some (Gval (Fuint 1) [::false])).
 { rewrite First. unfold top_environment. rewrite Env. exact InitialReset. }
 pose proof (legal_local_reset_history _ history 9259 false Steps Reset0) as Resets.
 rewrite <- Last. rewrite <- First in Dut0,Ref0. rewrite <- Last in Bubble.
 rewrite (rf_dut_nop_fullhistory_outputs _ history _ Dut0 Zero Instruction0 Steps index Index).
 rewrite (rf_reference_nop_fullhistory_outputs _ history _ Ref0 Zero Instruction0 Steps Resets Bubble index Index). reflexivity.
Qed.
