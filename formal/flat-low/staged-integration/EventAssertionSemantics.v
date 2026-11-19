Require Import CoreSocModel DUTRedirectReachability ExceptionEventHistory FormalLocalHistory.
From Coq Require Import ZArith Lia.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Theorem event_dut_valid_false_observed memory inputs k observed :
 generated_observe memory inputs k = Some observed ->
 generated_legal_trace memory inputs k ->
 VM.find 1 (formal_external_inputs (generated_observation_input inputs k)) = Some (Gval (Fuint 1) [::false]) ->
 VM.find 1469 (top_environment observed) = Some (Gval (Fuint 1) [::false]).
Proof.
 intros Observe Legal Reset.
 destruct (dut_no_trap_observed_context memory inputs k observed Observe Legal Reset)
 as [history [Last [Boundary [Steps NoTrap]]]].
 rewrite <- Last.
 exact (exception_event_after_five _ (history 9254%nat) (history 9255%nat) (history 9256%nat)
 (history 9257%nat) (history 9258%nat) (history 9259%nat) false
 (NoTrap 9254%nat ltac:(vm_compute;lia) ltac:(vm_compute;lia))
 (Steps 9254%nat ltac:(vm_compute;lia)) (Steps 9255%nat ltac:(vm_compute;lia))
 (Steps 9256%nat ltac:(vm_compute;lia)) (Steps 9257%nat ltac:(vm_compute;lia))
 (Steps 9258%nat ltac:(vm_compute;lia))).
Qed.
Require Import ReferenceEventNormalization ReferenceEventNodes ReferenceEventConnections NormalizedBit.
Theorem event_reference_disabled_history invalid s0 s1 s2 s3 s4 s5 :
 formal_value_iter invalid ComparisonNodes.flat_memories s0 false s0 ComparisonNodes.flat_statements = Some s1 ->
 formal_value_iter invalid ComparisonNodes.flat_memories s1 false s1 ComparisonNodes.flat_statements = Some s2 ->
 formal_value_iter invalid ComparisonNodes.flat_memories s2 false s2 ComparisonNodes.flat_statements = Some s3 ->
 formal_value_iter invalid ComparisonNodes.flat_memories s3 false s3 ComparisonNodes.flat_statements = Some s4 ->
 formal_value_iter invalid ComparisonNodes.flat_memories s4 false s4 ComparisonNodes.flat_statements = Some s5 ->
 VM.find 1707 s1 = Some (Gval (Fuint 1) [::false]) ->
 VM.find 1667 s5 = Some (Gval (Fuint 1) [::false]).
Proof.
 intros S1 S2 S3 S4 S5 Disabled.
 destruct (reference_event_7083_normalized invalid s0 s0 s1 S1) as [value [Value Normal]].
 pose proof (reference_event_7116_false invalid s0 s0 s1 S1) as No.
 assert (Selected : VM.find 7117 s2 = Some (Gval (Fuint 1) [::false])).
 { rewrite (reference_event_equation_7117 invalid s1 s1 s2 S2).
   cbn [reference_event_expr_7117 eval_hfexpr_with_memory eval_href_with_memory].
   rewrite Disabled Value No.
   unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref]. rewrite Value No.
   destruct Normal as [bit| | |]; try destruct bit; reflexivity. }
 assert (Alias : VM.find 7202 s3 = Some (Gval (Fuint 1) [::false])).
 { eapply reference_event_value_7202; [|reflexivity|exact S3].
   cbn [reference_event_expr_7202 eval_hfexpr_with_memory eval_href_with_memory]. exact Selected. }
 assert (Wire : VM.find 1857 s4 = Some (Gval (Fuint 1) [::false])).
 { eapply reference_event_connection_1857_value; [exact Alias|reflexivity|exact S4]. }
 eapply reference_event_connection_1667_value; [exact Wire|reflexivity|exact S5].
Qed.
Require Import FormalObservedHistory ReferenceControlStabilityHistory.
Theorem event_reference_disabled_observed memory inputs k observed :
 generated_observe memory inputs k = Some observed -> generated_legal_trace memory inputs k ->
 VM.find 1707 (top_environment observed) = Some (Gval (Fuint 1) [::false]) ->
 VM.find 1667 (top_environment observed) = Some (Gval (Fuint 1) [::false]).
Proof.
 intros Observe Legal Disabled.
 destruct (observed_history memory inputs k observed Observe Legal) as [bit [history [Last [Steps Resets]]]].
 assert (Earlier : VM.find 1707 (history 9255%nat) = Some (Gval (Fuint 1) [::false])).
 { rewrite (reference_control_stable_1707_history (generated_observation_input inputs k) nil history 9259 bit Resets Steps 9255 9259 ltac:(vm_compute;lia) ltac:(vm_compute;lia) ltac:(vm_compute;lia) (le_n 9259)) Last. exact Disabled. }
 rewrite <- Last.
 exact (event_reference_disabled_history _ (history 9254%nat) (history 9255%nat) (history 9256%nat)
 (history 9257%nat) (history 9258%nat) (history 9259%nat)
 (Steps 9254%nat ltac:(vm_compute;lia)) (Steps 9255%nat ltac:(vm_compute;lia))
 (Steps 9256%nat ltac:(vm_compute;lia)) (Steps 9257%nat ltac:(vm_compute;lia))
 (Steps 9258%nat ltac:(vm_compute;lia)) Earlier).
Qed.

Require Import ComparisonNodes JointBoundaryRegisters ConcreteRegisterInitialization ExceptionStabilityHistory FormalExceptionInput JointUpdateNodePositions JointUpdateExpressionCertificates.
From Coq Require Import List.
Theorem event_no_ecall_ebreak_history inputs path history limit time :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 (65 <= time)%coq_nat -> (time < limit)%coq_nat ->
 VM.find 128 (history time) = Some (Gval (Fuint 1) [::false]) ->
 dut_node_low_zero 290 (history time) /\ dut_node_low_zero 295 (history time).
Proof.
 intros Boundary Steps Lower Upper NoTrap.
 pose proof (Steps time Upper) as Step.
 assert (Zero442 : dut_node_low_zero 442 (history time)).
 { intros width bits Lookup.
   pose proof (exception_input_connection_128 (formal_invalid_policy inputs path) (history time) (history time) (history (S time)) _ _ Lookup (dut_adapt_low width bits) Step) as Value.
   rewrite <- (exception_stable_128_history inputs path history limit Boundary Steps time (S time) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) in Value.
   rewrite NoTrap in Value. inversion Value. reflexivity. }
 destruct (dut_or_low_recover 442 441 295 _ (history time) (history time) (history (S time))
  ltac:(apply (List.nth_error_In joint_update_expected_nodes 281%nat); vm_compute; reflexivity)
  (exception_concrete_441_history inputs path history limit Boundary Steps time ltac:(lia) ltac:(lia))
  (exception_concrete_295_history inputs path history limit Boundary Steps time ltac:(lia) ltac:(lia))
  (exception_stable_442_history inputs path history limit Boundary Steps time (S time) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) Zero442 Step)
  as [Zero441 Zero295].
 destruct (dut_or_low_recover 441 440 290 _ (history time) (history time) (history (S time))
  ltac:(apply (List.nth_error_In joint_update_expected_nodes 280%nat); vm_compute; reflexivity)
  (exception_concrete_440_history inputs path history limit Boundary Steps time ltac:(lia) ltac:(lia))
  (exception_concrete_290_history inputs path history limit Boundary Steps time ltac:(lia) ltac:(lia))
  (exception_stable_441_history inputs path history limit Boundary Steps time (S time) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) Zero441 Step)
  as [Zero440 Zero290].
 split; assumption.
Qed.
Theorem event_no_ecall_ebreak_observed memory inputs k observed :
 generated_observe memory inputs k = Some observed -> generated_legal_trace memory inputs k ->
 VM.find 1 (formal_external_inputs (generated_observation_input inputs k)) = Some (Gval (Fuint 1) [::false]) ->
 dut_node_low_zero 290 (top_environment observed) /\ dut_node_low_zero 295 (top_environment observed).
Proof.
 intros Observe Legal Reset.
 destruct (dut_no_trap_observed_context memory inputs k observed Observe Legal Reset)
 as [history [Last [Boundary [Steps NoTrap]]]].
 destruct (event_no_ecall_ebreak_history (generated_observation_input inputs k) nil history 9259 9258 Boundary Steps ltac:(vm_compute;lia) ltac:(vm_compute;lia)
 (NoTrap 9258 ltac:(vm_compute;lia) ltac:(vm_compute;lia))) as [Ecall Ebreak].
 rewrite <- Last. split; unfold dut_node_low_zero in *; intros width bits Value.
 - apply (Ecall width bits). rewrite (exception_stable_290_history (generated_observation_input inputs k) nil history 9259 Boundary Steps 9258 9259 ltac:(vm_compute;lia) ltac:(vm_compute;lia) ltac:(vm_compute;lia) (le_n 9259)). exact Value.
 - apply (Ebreak width bits). rewrite (exception_stable_295_history (generated_observation_input inputs k) nil history 9259 Boundary Steps 9258 9259 ltac:(vm_compute;lia) ltac:(vm_compute;lia) ltac:(vm_compute;lia) (le_n 9259)). exact Value.
Qed.
(* Actual privileged-instruction check. *)

Require Import ReferenceRedirectSpine.
Theorem event_privileged_bit8_history inputs path history limit time address bit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 (65 <= time)%coq_nat -> (time < limit)%coq_nat ->
 VM.find 128 (history time) = Some (Gval (Fuint 1) [::false]) ->
 VM.find 118 (history time) = Some (Gval (Fuint 3) [::false;false;true]) ->
 VM.find 140 (history time) = Some (Gval (Fuint 12) address) ->
 take 1 address = [::bit] -> drop 8 (take 9 address) = [::false] -> False.
Proof.
 intros Boundary Steps Lower Upper NoTrap Command Address Low High.
 pose proof (Steps time Upper) as Step.
 assert (V284 : VM.find 284 (history time) = Some (Gval (Fuint 1) [::true])).
 { rewrite (exception_stable_284_history inputs path history limit Boundary Steps time (S time) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)).
 eapply (reference_redirect_ground_step joint_update_node_offsets joint_update_expected_nodes 284 joint_update_expr_284);
 [exact joint_update_node_positions|exact joint_update_node_safety|apply (List.nth_error_In joint_update_expected_nodes 123%nat);vm_compute;reflexivity| |exact Step].
 intros site. cbn [joint_update_expr_284 eval_hfexpr_validif_policy eval_href_validif_policy].
 rewrite Command. destruct bit; reflexivity. }
 assert (V285 : VM.find 285 (history time) = Some (Gval (Fuint 1) [::bit])).
 { rewrite (exception_stable_285_history inputs path history limit Boundary Steps time (S time) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)).
 eapply (reference_redirect_ground_step joint_update_node_offsets joint_update_expected_nodes 285 joint_update_expr_285);
 [exact joint_update_node_positions|exact joint_update_node_safety|apply (List.nth_error_In joint_update_expected_nodes 124%nat);vm_compute;reflexivity| |exact Step].
 intros site. cbn [joint_update_expr_285 eval_hfexpr_validif_policy eval_href_validif_policy].
 rewrite Address. destruct address as [|b rest]; cbn in Low; inversion Low; subst; reflexivity. }
 assert (V286 : VM.find 286 (history time) = Some (Gval (Fuint 1) [::negb bit])).
 { rewrite (exception_stable_286_history inputs path history limit Boundary Steps time (S time) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)).
 eapply (reference_redirect_ground_step joint_update_node_offsets joint_update_expected_nodes 286 joint_update_expr_286);
 [exact joint_update_node_positions|exact joint_update_node_safety|apply (List.nth_error_In joint_update_expected_nodes 125%nat);vm_compute;reflexivity| |exact Step].
 intros site. cbn [joint_update_expr_286 eval_hfexpr_validif_policy eval_href_validif_policy].
 rewrite V285. destruct bit; reflexivity. }
 assert (V287 : VM.find 287 (history time) = Some (Gval (Fuint 1) [::negb bit])).
 { rewrite (exception_stable_287_history inputs path history limit Boundary Steps time (S time) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)).
 eapply (reference_redirect_ground_step joint_update_node_offsets joint_update_expected_nodes 287 joint_update_expr_287);
 [exact joint_update_node_positions|exact joint_update_node_safety|apply (List.nth_error_In joint_update_expected_nodes 126%nat);vm_compute;reflexivity| |exact Step].
 intros site. cbn [joint_update_expr_287 eval_hfexpr_validif_policy eval_href_validif_policy].
 rewrite V284 V286. destruct bit; reflexivity. }
 assert (V288 : VM.find 288 (history time) = Some (Gval (Fuint 1) [::false])).
 { rewrite (exception_stable_288_history inputs path history limit Boundary Steps time (S time) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)).
 eapply (reference_redirect_ground_step joint_update_node_offsets joint_update_expected_nodes 288 joint_update_expr_288);
 [exact joint_update_node_positions|exact joint_update_node_safety|apply (List.nth_error_In joint_update_expected_nodes 127%nat);vm_compute;reflexivity| |exact Step].
 intros site. cbn [joint_update_expr_288 eval_hfexpr_validif_policy eval_href_validif_policy].
 rewrite Address. cbn [eval_unop]. rewrite High. reflexivity. }
 assert (V289 : VM.find 289 (history time) = Some (Gval (Fuint 1) [::true])).
 { rewrite (exception_stable_289_history inputs path history limit Boundary Steps time (S time) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)).
 eapply (reference_redirect_ground_step joint_update_node_offsets joint_update_expected_nodes 289 joint_update_expr_289);
 [exact joint_update_node_positions|exact joint_update_node_safety|apply (List.nth_error_In joint_update_expected_nodes 128%nat);vm_compute;reflexivity| |exact Step].
 intros site. cbn [joint_update_expr_289 eval_hfexpr_validif_policy eval_href_validif_policy].
 rewrite V288. destruct bit; reflexivity. }
 assert (V290 : VM.find 290 (history time) = Some (Gval (Fuint 1) [::negb bit])).
 { rewrite (exception_stable_290_history inputs path history limit Boundary Steps time (S time) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)).
 eapply (reference_redirect_ground_step joint_update_node_offsets joint_update_expected_nodes 290 joint_update_expr_290);
 [exact joint_update_node_positions|exact joint_update_node_safety|apply (List.nth_error_In joint_update_expected_nodes 129%nat);vm_compute;reflexivity| |exact Step].
 intros site. cbn [joint_update_expr_290 eval_hfexpr_validif_policy eval_href_validif_policy].
 rewrite V287 V289. destruct bit; reflexivity. }
 assert (V291 : VM.find 291 (history time) = Some (Gval (Fuint 1) [::bit])).
 { rewrite (exception_stable_291_history inputs path history limit Boundary Steps time (S time) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)).
 eapply (reference_redirect_ground_step joint_update_node_offsets joint_update_expected_nodes 291 joint_update_expr_291);
 [exact joint_update_node_positions|exact joint_update_node_safety|apply (List.nth_error_In joint_update_expected_nodes 130%nat);vm_compute;reflexivity| |exact Step].
 intros site. cbn [joint_update_expr_291 eval_hfexpr_validif_policy eval_href_validif_policy].
 rewrite Address. destruct address as [|b rest]; cbn in Low; inversion Low; subst; reflexivity. }
 assert (V292 : VM.find 292 (history time) = Some (Gval (Fuint 1) [::bit])).
 { rewrite (exception_stable_292_history inputs path history limit Boundary Steps time (S time) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)).
 eapply (reference_redirect_ground_step joint_update_node_offsets joint_update_expected_nodes 292 joint_update_expr_292);
 [exact joint_update_node_positions|exact joint_update_node_safety|apply (List.nth_error_In joint_update_expected_nodes 131%nat);vm_compute;reflexivity| |exact Step].
 intros site. cbn [joint_update_expr_292 eval_hfexpr_validif_policy eval_href_validif_policy].
 rewrite V284 V291. destruct bit; reflexivity. }
 assert (V293 : VM.find 293 (history time) = Some (Gval (Fuint 1) [::false])).
 { rewrite (exception_stable_293_history inputs path history limit Boundary Steps time (S time) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)).
 eapply (reference_redirect_ground_step joint_update_node_offsets joint_update_expected_nodes 293 joint_update_expr_293);
 [exact joint_update_node_positions|exact joint_update_node_safety|apply (List.nth_error_In joint_update_expected_nodes 132%nat);vm_compute;reflexivity| |exact Step].
 intros site. cbn [joint_update_expr_293 eval_hfexpr_validif_policy eval_href_validif_policy].
 rewrite Address. cbn [eval_unop]. rewrite High. reflexivity. }
 assert (V294 : VM.find 294 (history time) = Some (Gval (Fuint 1) [::true])).
 { rewrite (exception_stable_294_history inputs path history limit Boundary Steps time (S time) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)).
 eapply (reference_redirect_ground_step joint_update_node_offsets joint_update_expected_nodes 294 joint_update_expr_294);
 [exact joint_update_node_positions|exact joint_update_node_safety|apply (List.nth_error_In joint_update_expected_nodes 133%nat);vm_compute;reflexivity| |exact Step].
 intros site. cbn [joint_update_expr_294 eval_hfexpr_validif_policy eval_href_validif_policy].
 rewrite V293. destruct bit; reflexivity. }
 assert (V295 : VM.find 295 (history time) = Some (Gval (Fuint 1) [::bit])).
 { rewrite (exception_stable_295_history inputs path history limit Boundary Steps time (S time) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)).
 eapply (reference_redirect_ground_step joint_update_node_offsets joint_update_expected_nodes 295 joint_update_expr_295);
 [exact joint_update_node_positions|exact joint_update_node_safety|apply (List.nth_error_In joint_update_expected_nodes 134%nat);vm_compute;reflexivity| |exact Step].
 intros site. cbn [joint_update_expr_295 eval_hfexpr_validif_policy eval_href_validif_policy].
 rewrite V292 V294. destruct bit; reflexivity. }
 destruct (event_no_ecall_ebreak_history inputs path history limit time Boundary Steps Lower Upper NoTrap) as [Ecall Ebreak].
 specialize (Ecall _ _ V290). specialize (Ebreak _ _ V295).
 destruct bit; discriminate.
Qed.
(* Observed privileged check. *)
Theorem event_privileged_bit8_observed memory inputs k observed address :
 generated_observe memory inputs k = Some observed -> generated_legal_trace memory inputs k ->
 VM.find 1 (formal_external_inputs (generated_observation_input inputs k)) = Some (Gval (Fuint 1) [::false]) ->
 VM.find 118 (top_environment observed) = Some (Gval (Fuint 3) [::false;false;true]) ->
 VM.find 140 (top_environment observed) = Some (Gval (Fuint 12) address) ->
 size address = 12%nat -> drop 8 (take 9 address) <> [::false].
Proof.
 intros Observe Legal Reset Command Address Size High.
 destruct address as [|bit rest]; [discriminate Size|].
 assert (Low : take 1 (bit::rest) = [::bit]).
 { change (bit :: take 0 rest = [::bit]). rewrite take0. reflexivity. }
 destruct (dut_no_trap_observed_context memory inputs k observed Observe Legal Reset)
 as [history [Last [Boundary [Steps NoTrap]]]].
 assert (Cmd : VM.find 118 (history 9258%nat) = Some (Gval (Fuint 3) [::false;false;true])).
 { rewrite (exception_stable_118_history (generated_observation_input inputs k) nil history 9259 Boundary Steps 9258 9259 ltac:(vm_compute;lia) ltac:(vm_compute;lia) ltac:(vm_compute;lia) (le_n 9259)) Last. exact Command. }
 assert (Addr : VM.find 140 (history 9258%nat) = Some (Gval (Fuint 12) (bit::rest))).
 { rewrite (exception_stable_140_history (generated_observation_input inputs k) nil history 9259 Boundary Steps 9258 9259 ltac:(vm_compute;lia) ltac:(vm_compute;lia) ltac:(vm_compute;lia) (le_n 9259)) Last. exact Address. }
 exact (event_privileged_bit8_history (generated_observation_input inputs k) nil history 9259 9258 (bit::rest) bit Boundary Steps ltac:(vm_compute;lia) ltac:(vm_compute;lia)
 (NoTrap 9258 ltac:(vm_compute;lia) ltac:(vm_compute;lia)) Cmd Addr Low High).
Qed.
Require Import FormalDeclaredConnection JointUpdateConnectionCertificates DUTRedirectDecode.
Theorem event_privileged_instruction_observed memory inputs k observed instruction :
 generated_observe memory inputs k = Some observed -> generated_legal_trace memory inputs k ->
 VM.find 1 (formal_external_inputs (generated_observation_input inputs k)) = Some (Gval (Fuint 1) [::false]) ->
 VM.find 7758 (top_environment observed) = Some (Gval (Fuint 3) [::false;false;true]) ->
 VM.find 7750 (top_environment observed) = Some (Gval (Fuint 32) instruction) ->
 size instruction = 32%nat ->
 drop 8 (take 9 (drop 20 (take 32 instruction))) <> [::false].
Proof.
 intros Observe Legal Reset Command Instruction Size.
 destruct (dut_no_trap_observed_context memory inputs k observed Observe Legal Reset)
 as [history [Last [Boundary [Steps NoTrap]]]].
 assert (CmdEarlier : VM.find 7758 (history 9258%nat) = Some (Gval (Fuint 3) [::false;false;true])).
 { rewrite (exception_stable_7758_history (generated_observation_input inputs k) nil history 9259 Boundary Steps 9258 9259 ltac:(vm_compute;lia) ltac:(vm_compute;lia) ltac:(vm_compute;lia) (le_n 9259)) Last. exact Command. }
 assert (InstEarlier : VM.find 7750 (history 9257%nat) = Some (Gval (Fuint 32) instruction)).
 { rewrite (exception_stable_7750_history (generated_observation_input inputs k) nil history 9259 Boundary Steps 9257 9259 ltac:(vm_compute;lia) ltac:(vm_compute;lia) ltac:(vm_compute;lia) (le_n 9259)) Last. exact Instruction. }
 assert (Cmd : VM.find 118 (history 9259%nat) = Some (Gval (Fuint 3) [::false;false;true])).
 { eapply (declared_connection_value 95 flat_statements joint_update_connection_118_decl joint_update_connection_118_mid joint_update_connection_118_tail 118 7758 3 (Gval (Fuint 3) [::false;false;true]));
 [exact joint_update_connection_118_position|exact joint_update_connection_118_split|exact joint_update_connection_118_straight|exact joint_update_connection_118_mid_safe|exact joint_update_connection_118_tail_safe|exact joint_update_connection_118_nonregister|reflexivity|exact CmdEarlier|reflexivity|apply Steps;vm_compute;lia]. }
 assert (Inst : VM.find 123 (history 9258%nat) = Some (Gval (Fuint 32) instruction)).
 { eapply (declared_connection_value 100 flat_statements joint_update_connection_123_decl joint_update_connection_123_mid joint_update_connection_123_tail 123 7750 32 (Gval (Fuint 32) instruction));
 [exact joint_update_connection_123_position|exact joint_update_connection_123_split|exact joint_update_connection_123_straight|exact joint_update_connection_123_mid_safe|exact joint_update_connection_123_tail_safe|exact joint_update_connection_123_nonregister|reflexivity|exact InstEarlier|apply dut_decode_adapt;exact Size|apply Steps;vm_compute;lia]. }
 assert (Addr : VM.find 140 (history 9259%nat) = Some (Gval (Fuint 12) (drop 20 (take 32 instruction)))).
 { eapply (reference_redirect_ground_step joint_update_node_offsets joint_update_expected_nodes 140 joint_update_expr_140);
 [exact joint_update_node_positions|exact joint_update_node_safety|apply (List.nth_error_In joint_update_expected_nodes 0%nat);vm_compute;reflexivity| |apply Steps;vm_compute;lia].
 intros site. cbn [joint_update_expr_140 eval_hfexpr_validif_policy eval_href_validif_policy]. rewrite Inst. reflexivity. }
 rewrite Last in Cmd,Addr.
 apply (event_privileged_bit8_observed memory inputs k observed (drop 20 (take 32 instruction)) Observe Legal Reset Cmd Addr).
 rewrite size_drop size_take Size. reflexivity.
Qed.
Lemma event_csr_bit8 instruction :
 size instruction = 32%nat ->
 drop 8 (take 9 (drop 20 (take 32 instruction))) = [::seq.nth false instruction 28].
Proof.
 intro Size.
 set slice := drop 8 (take 9 (drop 20 (take 32 instruction))).
 assert (Length : size slice = 1%nat).
 { unfold slice. rewrite size_drop size_take size_drop size_take Size. reflexivity. }
 assert (Bit : seq.nth false slice 0 = seq.nth false instruction 28).
 { unfold slice. rewrite nth_drop nth_take; [|reflexivity].
   rewrite nth_drop nth_take; [reflexivity|reflexivity]. }
 change (slice = [::seq.nth false instruction 28]).
 destruct slice as [|b tail]; [discriminate Length|].
 destruct tail as [|c tail]; [|discriminate Length].
 cbn in Bit. rewrite Bit. reflexivity.
Qed.
Theorem event_privileged_instruction_bit28 memory inputs k observed instruction :
 generated_observe memory inputs k = Some observed -> generated_legal_trace memory inputs k ->
 VM.find 1 (formal_external_inputs (generated_observation_input inputs k)) = Some (Gval (Fuint 1) [::false]) ->
 VM.find 7758 (top_environment observed) = Some (Gval (Fuint 3) [::false;false;true]) ->
 VM.find 7750 (top_environment observed) = Some (Gval (Fuint 32) instruction) ->
 size instruction = 32%nat -> seq.nth false instruction 28 = true.
Proof.
 intros Observe Legal Reset Command Instruction Size.
 pose proof (event_privileged_instruction_observed memory inputs k observed instruction Observe Legal Reset Command Instruction Size) as NotZero.
 rewrite (event_csr_bit8 instruction Size) in NotZero.
 destruct (seq.nth false instruction 28); [reflexivity|].
 exfalso. apply NotZero. reflexivity.
Qed.
Print Assumptions event_csr_bit8.
Require Import CSRCommandCorrespondence.
From nbits Require Import NBits.
Theorem event_no_ecall_ebreak_instruction memory inputs k observed instruction lane :
 generated_observe memory inputs k = Some observed -> generated_legal_trace memory inputs k ->
 VM.find 1 (formal_external_inputs (generated_observation_input inputs k)) = Some (Gval (Fuint 1) [::false]) ->
 (lane < 2)%coq_nat ->
 VM.find 7750 (top_environment observed) = Some (Gval (Fuint 32) instruction) ->
 ~csr_system_instruction instruction lane.
Proof.
 intros Observe Legal Reset Lane Instruction Code.
 pose proof (csr_system_observed memory inputs k observed Observe Legal instruction lane Lane Instruction Code) as Command.
 assert (Size : size instruction = 32%nat).
 { unfold csr_system_instruction in Code. rewrite Code. apply size_from_N. }
 pose proof (event_privileged_instruction_bit28 memory inputs k observed instruction Observe Legal Reset Command Instruction Size) as Bit.
 unfold csr_system_instruction in Code. rewrite Code in Bit.
 do 2 (destruct lane as [|lane]; [vm_compute in Bit;discriminate|]). lia.
Qed.
