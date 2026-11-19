Require Import CoreSocModel ComparisonNodes ReferenceMemoryRequest RFReferenceNopInputs ReferenceControlStabilityHistory ReferenceControlNodeCongruence0 ReferenceControlNodeCertificates0 ReferenceControlExpressions ReferenceRedirectSpine DUTRedirectDecode LoadTypeCorrespondence FormalDeclaredWireCheck JointBoundaryRegisters JointUpdateBoundaryHistory ObservedJointRegisterConcrete FormalObservedHistory FormalLocalHistory.
From Coq Require Import NArith ZArith List Lia.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From nbits Require Import NBits.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Firrtl_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Local Opaque flat_statements flat_memories generated_modules generated_top.
Definition memory_reference_instruction instruction enabled := if enabled then instruction else from_N 32 0.
Theorem memory_reference_instruction_history invalid history limit start instruction enabled :
 size instruction = 32%nat ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter invalid flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 (forall i, (i <= limit)%coq_nat -> VM.find 7750 (history i) = Some (Gval (Fuint 32) instruction)) ->
 (forall i, (start <= i)%coq_nat -> (i <= limit)%coq_nat -> VM.find 1707 (history i) = Some (Gval (Fuint 1) [::enabled])) ->
 forall time, (Nat.add start 5 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 VM.find 1884 (history time) = Some (Gval (Fuint 32) (memory_reference_instruction instruction enabled)).
Proof.
 intros Size Steps Instruction Enabled [|[|[|[|[|time]]]]] Lower Upper;try lia.
 assert (A : VM.find 1396 (history (S time)) = Some (Gval (Fuint 32) instruction)).
 { eapply declared_wire_checked_value with (old:=history time);[exact rf_reference_input_1396_certificate|apply Instruction;lia|apply dut_decode_adapt;exact Size|apply Steps;lia]. }
 assert (B : VM.find 1516 (history (S (S time))) = Some (Gval (Fuint 32) instruction)).
 { eapply declared_wire_checked_value;[exact rf_reference_input_1516_certificate|exact A|apply dut_decode_adapt;exact Size|apply Steps;lia]. }
 assert (C : VM.find 1706 (history (S (S (S time)))) = Some (Gval (Fuint 32) instruction)).
 { eapply declared_wire_checked_value;[exact rf_reference_input_1706_certificate|exact B|apply dut_decode_adapt;exact Size|apply Steps;lia]. }
 assert (D : VM.find 1883 (history (S (S (S (S time))))) = Some (Gval (Fuint 32) (memory_reference_instruction instruction enabled))).
 { eapply (reference_redirect_ground_step reference_control_0_offsets reference_control_0_nodes 1883 reference_control_expr_1883);
 [exact reference_control_0_positions|exact reference_control_0_safety|exact reference_control_member_1883| |apply Steps;lia].
 intros site. cbn [reference_control_expr_1883 eval_hfexpr_validif_policy eval_href_validif_policy].
 rewrite (Enabled (S (S (S time))) ltac:(lia) ltac:(lia)). destruct enabled;cbn.
 - rewrite C. apply dut_decode_adapt;exact Size.
 - unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref]. rewrite C. reflexivity. }
 eapply (reference_redirect_ground_step reference_control_0_offsets reference_control_0_nodes 1884 reference_control_expr_1884);
 [exact reference_control_0_positions|exact reference_control_0_safety|exact reference_control_member_1884| |apply Steps;lia].
 intros site;exact D.
Qed.
Theorem memory_reference_decode_observed memory inputs k observed instruction enabled row :
 generated_observe memory inputs k = Some observed -> generated_legal_trace memory inputs k ->
 (row < 8)%coq_nat ->
 VM.find 7750 (top_environment observed) = Some (Gval (Fuint 32) instruction) ->
 VM.find 1707 (top_environment observed) = Some (Gval (Fuint 1) [::enabled]) ->
 VM.find (reference_memory_guard row) (top_environment observed) = Some (Gval (Fuint 1)
 [::N.eqb (reference_memory_code row) (N.land (to_N (memory_reference_instruction instruction enabled)) 28799)]).
Proof.
 intros Observe Legal Row Instruction Enabled.
 destruct (observed_joint_register_concrete memory inputs k observed 7750%nat 32%nat Observe Legal load_type_instruction_member) as [word [Size Word]].
 rewrite Instruction in Word. inversion Word;subst word.
 destruct (observed_history memory inputs k observed Observe Legal) as [reset [history [Last [Steps Resets]]]].
 assert (Inst : forall t, (t <= 9259)%coq_nat -> VM.find 7750 (history t) = Some (Gval (Fuint 32) instruction)).
 { intros t Upper. pose proof (joint_update_register_history_same _ history 9259 7750 32 load_type_instruction_member Steps) as Hold.
   rewrite (Hold t Upper). rewrite <- (Hold 9259%nat ltac:(lia)). rewrite Last. exact Instruction. }
 assert (Enable : forall t, (200 <= t)%coq_nat -> (t <= 9259)%coq_nat -> VM.find 1707 (history t) = Some (Gval (Fuint 1) [::enabled])).
 { intros t Lower Upper. rewrite (reference_control_stable_1707_history (generated_observation_input inputs k) nil history 9259 reset Resets Steps t 9259%nat ltac:(lia) ltac:(lia) Upper ltac:(lia)) Last. exact Enabled. }
 assert (Source : forall t, (205 <= t)%coq_nat -> (t <= 9259)%coq_nat -> VM.find 1884 (history t) = Some (Gval (Fuint 32) (memory_reference_instruction instruction enabled))).
 { intros t Lower Upper. exact (memory_reference_instruction_history _ history 9259 200 instruction enabled Size Steps Inst Enable t Lower Upper). }
 pose proof (reference_memory_decode_history (formal_invalid_policy (generated_observation_input inputs k) nil) (fun t => history (Nat.add 205 t)) 9054 (memory_reference_instruction instruction enabled) row Row) as Decode.
 assert (ShiftSteps : forall i, (i < 9054)%coq_nat -> formal_value_iter (formal_invalid_policy (generated_observation_input inputs k) nil) flat_memories (history (Nat.add 205 i)) false (history (Nat.add 205 i)) flat_statements = Some (history (Nat.add 205 (S i)))).
 { intros i Bound. replace (Nat.add 205 (S i)) with (S (Nat.add 205 i)) by lia. apply Steps. eapply Nat.lt_le_trans;[apply Nat.add_lt_mono_l;exact Bound|vm_compute;lia]. }
 specialize (Decode ShiftSteps ltac:(intros i Bound;apply Source;[lia|eapply Nat.le_trans;[apply Nat.add_le_mono_l;exact Bound|vm_compute;lia]]) 9054 ltac:(vm_compute;lia) (Nat.le_refl _)).
 change (VM.find (reference_memory_guard row) (history 9259%nat) = Some (Gval (Fuint 1) [::N.eqb (reference_memory_code row) (N.land (to_N (memory_reference_instruction instruction enabled)) 28799)])) in Decode.
 rewrite Last in Decode. exact Decode.
Qed.
Require Import ReferenceMemoryAlignment ReferenceLoadSemantics MemoryRequestWidth ReferenceRequestSpine MemoryRequestCorrespondence LoadPipelineClassification.
Definition memory_request_observed_guards instruction enabled address (node:VarOrder.T) : bool :=
 match node with
 | 1707 => enabled
 | 1886 => N.eqb 20483 (N.land (to_N (memory_reference_instruction instruction enabled)) 28799)
 | 1958 => N.eqb 16387 (N.land (to_N (memory_reference_instruction instruction enabled)) 28799)
 | 1962 => N.eqb 8195 (N.land (to_N (memory_reference_instruction instruction enabled)) 28799)
 | 1966 => N.eqb 4099 (N.land (to_N (memory_reference_instruction instruction enabled)) 28799)
 | 1970 => N.eqb 3 (N.land (to_N (memory_reference_instruction instruction enabled)) 28799)
 | 1951 => N.eqb 35 (N.land (to_N (memory_reference_instruction instruction enabled)) 28799)
 | 1946 => N.eqb 4131 (N.land (to_N (memory_reference_instruction instruction enabled)) 28799)
 | 1941 => N.eqb 8227 (N.land (to_N (memory_reference_instruction instruction enabled)) 28799)
 | 2565 => reference_alignment_test 0 (nth false address 0) (nth false address 1)
 | 2649 => reference_alignment_test 1 (nth false address 0) (nth false address 1)
 | 2664 => reference_alignment_test 2 (nth false address 0) (nth false address 1)
 | 2679 => true
 | 2708 => reference_alignment_test 4 (nth false address 0) (nth false address 1)
 | 2723 => reference_alignment_test 5 (nth false address 0) (nth false address 1)
 | _ => false end.
Theorem memory_request_all_guards_observed memory inputs k observed instruction enabled rs1 immediate :
 generated_observe memory inputs k = Some observed -> generated_legal_trace memory inputs k ->
 VM.find 7750 (top_environment observed) = Some (Gval (Fuint 32) instruction) ->
 VM.find 1707 (top_environment observed) = Some (Gval (Fuint 1) [::enabled]) ->
 VM.find 2209 (top_environment observed) = Some (Gval (Fuint 32) rs1) ->
 VM.find 2552 (top_environment observed) = Some (Gval (Fuint 32) immediate) ->
 forall node, List.In node reference_request_guard_nodes ->
 VM.find node (top_environment observed) = Some (Gval (Fuint 1) [::memory_request_observed_guards instruction enabled (reference_load_address rs1 immediate) node]).
Proof.
 intros Observe Legal Instruction Enabled Rs1 Imm node Member.
 cbn [reference_request_guard_nodes List.In] in Member.
 repeat destruct Member as [<-|Member];try contradiction.
 - exact Enabled.
 - exact (memory_reference_decode_observed memory inputs k observed instruction enabled 0%nat Observe Legal ltac:(lia) Instruction Enabled).
 - exact (memory_reference_decode_observed memory inputs k observed instruction enabled 7%nat Observe Legal ltac:(lia) Instruction Enabled).
 - exact (memory_reference_decode_observed memory inputs k observed instruction enabled 6%nat Observe Legal ltac:(lia) Instruction Enabled).
 - exact (memory_reference_decode_observed memory inputs k observed instruction enabled 5%nat Observe Legal ltac:(lia) Instruction Enabled).
 - exact (memory_reference_decode_observed memory inputs k observed instruction enabled 1%nat Observe Legal ltac:(lia) Instruction Enabled).
 - exact (memory_reference_decode_observed memory inputs k observed instruction enabled 2%nat Observe Legal ltac:(lia) Instruction Enabled).
 - exact (memory_reference_decode_observed memory inputs k observed instruction enabled 3%nat Observe Legal ltac:(lia) Instruction Enabled).
 - exact (memory_reference_decode_observed memory inputs k observed instruction enabled 4%nat Observe Legal ltac:(lia) Instruction Enabled).
 - exact (reference_alignment_observed memory inputs k observed 0%nat rs1 immediate Observe Legal ltac:(lia) Rs1 Imm).
 - exact (reference_alignment_observed memory inputs k observed 1%nat rs1 immediate Observe Legal ltac:(lia) Rs1 Imm).
 - exact (reference_alignment_observed memory inputs k observed 2%nat rs1 immediate Observe Legal ltac:(lia) Rs1 Imm).
 - exact (reference_alignment_observed memory inputs k observed 3%nat rs1 immediate Observe Legal ltac:(lia) Rs1 Imm).
 - exact (reference_alignment_observed memory inputs k observed 4%nat rs1 immediate Observe Legal ltac:(lia) Rs1 Imm).
 - exact (reference_alignment_observed memory inputs k observed 5%nat rs1 immediate Observe Legal ltac:(lia) Rs1 Imm).
Qed.
Definition memory_request_load_aligned lane address :=
 match lane with O => negb (nth false address 0) | S O => true
 | S (S O) => negb (nth false address 0 || nth false address 1)
 | S (S (S O)) => negb (nth false address 0) | _ => true end.
Theorem memory_request_load_width_observed memory inputs k observed instruction lane rs1 immediate :
 generated_observe memory inputs k = Some observed -> generated_legal_trace memory inputs k ->
 VM.find 1 (formal_external_inputs (generated_observation_input inputs k)) = Some (Gval (Fuint 1) [::false]) ->
 (lane < 5)%coq_nat -> VM.find 7750 (top_environment observed) = Some (Gval (Fuint 32) instruction) ->
 load_type_is_load instruction lane ->
 VM.find 2209 (top_environment observed) = Some (Gval (Fuint 32) rs1) ->
 VM.find 2552 (top_environment observed) = Some (Gval (Fuint 32) immediate) ->
 memory_request_load_aligned lane (reference_load_address rs1 immediate) = true ->
 VM.find 1476 (top_environment observed) = VM.find 1521 (top_environment observed) /\
 VM.find 1519 (top_environment observed) = Some (Gval (Fuint 1) [::true]) /\
 VM.find 1523 (top_environment observed) = Some (Gval (Fuint 1) [::false]).
Proof.
 intros Observe Legal Reset Lane Instruction Load Rs1 Imm Align.
 destruct (load_pipeline_load_reference_enabled memory inputs k observed instruction lane Observe Legal Reset Lane Instruction Load) as [Valid Enabled].
 eapply (memory_load_request_width_correspondence memory inputs k observed instruction lane (memory_request_observed_guards instruction true (reference_load_address rs1 immediate)));
 [exact Observe|exact Legal|exact Lane|exact Instruction|exact Load| |reflexivity| |].
 - exact (memory_request_all_guards_observed memory inputs k observed instruction true rs1 immediate Observe Legal Instruction Enabled Rs1 Imm).
 - intros row Row. pose proof (reference_memory_decode_load (to_N instruction) lane row Lane Row Load) as Decode.
   do 8 (destruct row as [|row];[exact Decode|]);lia.
 - do 5 (destruct lane as [|lane];[exact Align|]);lia.
Qed.
Lemma memory_request_decode_zero instruction : load_type_decode instruction 49 = from_N 3 0 ->
 forall lane, (lane < 5)%coq_nat -> N.land instruction 28799 <> load_type_lane_code lane.
Proof.
 intros Zero lane Lane Code. rewrite (load_type_decode_load instruction lane Lane Code) in Zero.
 do 5 (destruct lane as [|lane];[discriminate Zero|]);lia.
Qed.
Lemma memory_request_read_zero guards :
 (forall row, (row < 5)%coq_nat -> guards (reference_memory_guard row) = false) ->
 reference_request_width false guards = 0 /\ reference_request_valid false guards = false.
Proof.
 intro Decode. pose proof (Decode 0%nat ltac:(lia)) as D0.
 pose proof (Decode 1%nat ltac:(lia)) as D1. pose proof (Decode 2%nat ltac:(lia)) as D2.
 pose proof (Decode 3%nat ltac:(lia)) as D3. pose proof (Decode 4%nat ltac:(lia)) as D4.
 cbn [reference_memory_guard reference_memory_guards nth] in D0,D1,D2,D3,D4.
 unfold reference_request_width,reference_request_valid. rewrite D0 D1 D2 D3 D4.
 destruct (guards 1707);split;reflexivity.
Qed.
Theorem memory_dut_zero_width_observed memory inputs k observed :
 generated_observe memory inputs k = Some observed -> generated_legal_trace memory inputs k ->
 VM.find 7755 (top_environment observed) = Some (Gval (Fuint 3) (from_N 3 0)) ->
 VM.find 1476 (top_environment observed) = Some (Gval (Fuint 6) (from_N 6 0)).
Proof.
 intros Observe Legal Mode.
 destruct (observed_history memory inputs k observed Observe Legal) as [reset [history [Last [Steps Resets]]]].
 assert (Source : forall i, (i <= 9259)%coq_nat -> VM.find 7755 (history i) = Some (Gval (Fuint 3) (from_N 3 0))).
 { intros i Upper. pose proof (joint_update_register_history_same _ history 9259 7755 3 load_type_register_member Steps) as Hold.
   rewrite (Hold i Upper). rewrite <- (Hold 9259%nat ltac:(lia)). rewrite Last. exact Mode. }
 rewrite <- Last. eapply (memory_width_alias_history false);[apply size_from_N|exact Steps| |vm_compute;lia|vm_compute;lia].
 intros i Lower Upper. exact (memory_width_decoder_history false 0%nat _ history 9259 ltac:(vm_compute;lia) Steps Source i Lower Upper).
Qed.
Theorem memory_read_zero_width_observed memory inputs k observed instruction enabled rs1 immediate :
 generated_observe memory inputs k = Some observed -> generated_legal_trace memory inputs k ->
 VM.find 7750 (top_environment observed) = Some (Gval (Fuint 32) instruction) ->
 load_type_decode (to_N instruction) 49 = from_N 3 0 ->
 VM.find 1707 (top_environment observed) = Some (Gval (Fuint 1) [::enabled]) ->
 VM.find 2209 (top_environment observed) = Some (Gval (Fuint 32) rs1) ->
 VM.find 2552 (top_environment observed) = Some (Gval (Fuint 32) immediate) ->
 VM.find 1476 (top_environment observed) = VM.find 1521 (top_environment observed).
Proof.
 intros Observe Legal Instruction Zero Enabled Rs1 Imm.
 pose proof (load_pipeline_observed memory inputs k observed Observe Legal instruction Instruction) as Mode. rewrite Zero in Mode.
 pose proof (memory_dut_zero_width_observed memory inputs k observed Observe Legal Mode) as Dut.
 pose proof (memory_request_all_guards_observed memory inputs k observed instruction enabled rs1 immediate Observe Legal Instruction Enabled Rs1 Imm) as Guards.
 destruct (reference_request_observed memory inputs k observed _ false Observe Legal Guards) as [Valid Width].
 assert (D : forall row, (row < 5)%coq_nat -> memory_request_observed_guards instruction enabled (reference_load_address rs1 immediate) (reference_memory_guard row) = false).
 { intros row Row. pose proof (memory_request_decode_zero (to_N instruction) Zero row Row) as NotLoad.
   assert (Codes : reference_memory_code row = load_type_lane_code row).
   { do 5 (destruct row as [|row];[reflexivity|]);lia. }
   assert (Test : N.eqb (reference_memory_code row) (N.land (to_N (memory_reference_instruction instruction enabled)) 28799) = false).
   { destruct enabled.
     - apply N.eqb_neq. rewrite Codes. unfold memory_reference_instruction. intro E. apply NotLoad. symmetry;exact E.
     - do 5 (destruct row as [|row];[reflexivity|]);lia. }
   do 5 (destruct row as [|row];[exact Test|]);lia. }
 rewrite (proj1 (memory_request_read_zero _ D)) in Width. rewrite Dut Width. reflexivity.
Qed.
Require Import CheckerValidBubbleValue ObservedLegalNoTrap FormalResetPreparation.
Theorem memory_reference_enable_known memory inputs k observed :
 generated_observe memory inputs k = Some observed -> generated_legal_trace memory inputs k ->
 VM.find 1 (formal_external_inputs (generated_observation_input inputs k)) = Some (Gval (Fuint 1) [::false]) ->
 exists enabled, VM.find 1707 (top_environment observed) = Some (Gval (Fuint 1) [::enabled]).
Proof.
 intros Observe Legal Reset.
 destruct (load_pipeline_late_observed memory inputs k observed Observe Legal) as [bubble [Late Nop]].
 destruct (observed_legal_no_trap_history memory inputs k observed Observe Legal Reset)
 as [committed [initial [history [Run [Prepare [First [Last [Steps NoTrap]]]]]]]].
 destruct (top_reset_prepared (Some committed) _ initial _ Reset Prepare) as [env [Env InitialReset]].
 assert (Reset0 : VM.find 1 (history 0%nat) = Some (Gval (Fuint 1) [::false])).
 { rewrite First. unfold top_environment. rewrite Env. exact InitialReset. }
 pose proof (legal_local_reset_history _ history 9259 false Steps Reset0) as Resets.
 pose proof (checker_valid_history_from_bubble _ history bubble Steps Resets ltac:(rewrite Last;exact Late)) as Valid.
 assert (V : forall t, (200 <= t)%coq_nat -> (t <= 9259)%coq_nat -> VM.find 1395 (history t) = Some (Gval (Fuint 1) [::negb bubble])).
 { intros t Lower Upper. rewrite (reference_control_stable_1395_history (generated_observation_input inputs k) nil history 9259 false Resets Steps t 9259%nat ltac:(lia) ltac:(lia) Upper ltac:(lia)). exact Valid. }
 exists (negb bubble). rewrite <- Last.
 eapply declared_wire_checked_value with (source_value:=Gval (Fuint 1) [::negb bubble]);[exact rf_reference_input_1707_certificate| |reflexivity|exact (Steps 9258%nat ltac:(vm_compute;lia))].
 eapply declared_wire_checked_value;[exact rf_reference_input_1517_certificate|exact (V 9257%nat ltac:(vm_compute;lia) ltac:(vm_compute;lia))| |exact (Steps 9257%nat ltac:(vm_compute;lia))].
 destruct bubble;reflexivity.
Qed.
Theorem memory_read_width_correspondence memory inputs k observed instruction rs1 immediate :
 generated_observe memory inputs k = Some observed -> generated_legal_trace memory inputs k ->
 VM.find 1 (formal_external_inputs (generated_observation_input inputs k)) = Some (Gval (Fuint 1) [::false]) ->
 VM.find 7750 (top_environment observed) = Some (Gval (Fuint 32) instruction) ->
 VM.find 2209 (top_environment observed) = Some (Gval (Fuint 32) rs1) ->
 VM.find 2552 (top_environment observed) = Some (Gval (Fuint 32) immediate) ->
 (forall lane, (lane < 5)%coq_nat -> load_type_is_load instruction lane -> memory_request_load_aligned lane (reference_load_address rs1 immediate) = true) ->
 VM.find 1476 (top_environment observed) = VM.find 1521 (top_environment observed).
Proof.
 intros Observe Legal Reset Instruction Rs1 Imm Align.
 destruct (load_pipeline_decode_classify (to_N instruction) 49 ltac:(lia)) as [Zero|[lane [Lane [Load Mode]]]].
 - destruct (memory_reference_enable_known memory inputs k observed Observe Legal Reset) as [enabled Enabled].
   exact (memory_read_zero_width_observed memory inputs k observed instruction enabled rs1 immediate Observe Legal Instruction Zero Enabled Rs1 Imm).
 - exact (proj1 (memory_request_load_width_observed memory inputs k observed instruction lane rs1 immediate Observe Legal Reset Lane Instruction Load Rs1 Imm (Align lane Lane Load))).
Qed.
