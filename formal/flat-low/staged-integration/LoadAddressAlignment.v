Require Import CoreSocModel ComparisonNodes DUTRedirectReachability ReferenceRedirectSpine
 JointUpdateNodePositions JointUpdateExpressionCertificates ExceptionStabilityHistory
 JointBoundaryRegisters ConcreteRegisterInitialization.
From Coq Require Import NArith ZArith Lia List.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From nbits Require Import NBitsDef NBitsOp.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths
 HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Local Opaque flat_statements flat_memories generated_modules generated_top.
Theorem load_word_invalid_history inputs path history limit time b0 b1 rest :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 (65 <= time)%coq_nat -> (time < limit)%coq_nat ->
 VM.find 126 (history time) = Some (Gval (Fuint 3) [::true;false;false]) ->
 VM.find 122 (history time) = Some (Gval (Fuint 32) (b0::b1::rest)) ->
 VM.find 418 (history time) = Some (Gval (Fuint 1) [::b0 || b1]).
Proof.
 intros Boundary Steps Lower Upper Mode Address.
 pose proof (Steps time Upper) as Step.
 assert (V409 : VM.find 409 (history time) = Some (Gval (Fuint 2) [::b0;b1])).
 { rewrite (exception_stable_409_history inputs path history limit Boundary Steps time (S time) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)).
   eapply (reference_redirect_ground_step joint_update_node_offsets joint_update_expected_nodes 409 joint_update_expr_409);
   [exact joint_update_node_positions|exact joint_update_node_safety|apply (List.nth_error_In joint_update_expected_nodes 248%nat); vm_compute;reflexivity| |exact Step].
   intros site. cbn [joint_update_expr_409 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
   rewrite Address. unfold eval_type_of_expr; cbn [type_of_expr' eval_type_of_ref]; rewrite ?Address. destruct b0,b1,rest; reflexivity. }
 assert (V410 : VM.find 410 (history time) = Some (Gval (Fuint 1) [::b0 || b1])).
 { rewrite (exception_stable_410_history inputs path history limit Boundary Steps time (S time) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)).
   eapply (reference_redirect_ground_step joint_update_node_offsets joint_update_expected_nodes 410 joint_update_expr_410);
   [exact joint_update_node_positions|exact joint_update_node_safety|apply (List.nth_error_In joint_update_expected_nodes 249%nat); vm_compute;reflexivity| |exact Step].
   intros site. cbn [joint_update_expr_410 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
   rewrite V409. unfold eval_type_of_expr; cbn [type_of_expr' eval_type_of_ref]; rewrite ?V409. destruct b0,b1,rest; reflexivity. }
 assert (V411 : VM.find 411 (history time) = Some (Gval (Fuint 1) [::b0])).
 { rewrite (exception_stable_411_history inputs path history limit Boundary Steps time (S time) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)).
   eapply (reference_redirect_ground_step joint_update_node_offsets joint_update_expected_nodes 411 joint_update_expr_411);
   [exact joint_update_node_positions|exact joint_update_node_safety|apply (List.nth_error_In joint_update_expected_nodes 250%nat); vm_compute;reflexivity| |exact Step].
   intros site. cbn [joint_update_expr_411 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
   rewrite Address. unfold eval_type_of_expr; cbn [type_of_expr' eval_type_of_ref]; rewrite ?Address. destruct b0,b1,rest; reflexivity. }
 assert (V412 : VM.find 412 (history time) = Some (Gval (Fuint 1) [::b0])).
 { rewrite (exception_stable_412_history inputs path history limit Boundary Steps time (S time) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)).
   eapply (reference_redirect_ground_step joint_update_node_offsets joint_update_expected_nodes 412 joint_update_expr_412);
   [exact joint_update_node_positions|exact joint_update_node_safety|apply (List.nth_error_In joint_update_expected_nodes 251%nat); vm_compute;reflexivity| |exact Step].
   intros site. cbn [joint_update_expr_412 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
   rewrite Address. unfold eval_type_of_expr; cbn [type_of_expr' eval_type_of_ref]; rewrite ?Address. destruct b0,b1,rest; reflexivity. }
 assert (V413 : VM.find 413 (history time) = Some (Gval (Fuint 1) [::true])).
 { rewrite (exception_stable_413_history inputs path history limit Boundary Steps time (S time) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)).
   eapply (reference_redirect_ground_step joint_update_node_offsets joint_update_expected_nodes 413 joint_update_expr_413);
   [exact joint_update_node_positions|exact joint_update_node_safety|apply (List.nth_error_In joint_update_expected_nodes 252%nat); vm_compute;reflexivity| |exact Step].
   intros site. cbn [joint_update_expr_413 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
   rewrite Mode. unfold eval_type_of_expr; cbn [type_of_expr' eval_type_of_ref]; rewrite ?Mode. destruct b0,b1,rest; reflexivity. }
 assert (V414 : VM.find 414 (history time) = Some (Gval (Fuint 1) [::b0 || b1])).
 { rewrite (exception_stable_414_history inputs path history limit Boundary Steps time (S time) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)).
   eapply (reference_redirect_ground_step joint_update_node_offsets joint_update_expected_nodes 414 joint_update_expr_414);
   [exact joint_update_node_positions|exact joint_update_node_safety|apply (List.nth_error_In joint_update_expected_nodes 253%nat); vm_compute;reflexivity| |exact Step].
   intros site. cbn [joint_update_expr_414 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
   rewrite V413 V410. unfold eval_type_of_expr; cbn [type_of_expr' eval_type_of_ref]; rewrite ?V413 ?V410. destruct b0,b1,rest; reflexivity. }
 assert (V415 : VM.find 415 (history time) = Some (Gval (Fuint 1) [::false])).
 { rewrite (exception_stable_415_history inputs path history limit Boundary Steps time (S time) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)).
   eapply (reference_redirect_ground_step joint_update_node_offsets joint_update_expected_nodes 415 joint_update_expr_415);
   [exact joint_update_node_positions|exact joint_update_node_safety|apply (List.nth_error_In joint_update_expected_nodes 254%nat); vm_compute;reflexivity| |exact Step].
   intros site. cbn [joint_update_expr_415 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
   rewrite Mode. unfold eval_type_of_expr; cbn [type_of_expr' eval_type_of_ref]; rewrite ?Mode. destruct b0,b1,rest; reflexivity. }
 assert (V416 : VM.find 416 (history time) = Some (Gval (Fuint 1) [::b0 || b1])).
 { rewrite (exception_stable_416_history inputs path history limit Boundary Steps time (S time) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)).
   eapply (reference_redirect_ground_step joint_update_node_offsets joint_update_expected_nodes 416 joint_update_expr_416);
   [exact joint_update_node_positions|exact joint_update_node_safety|apply (List.nth_error_In joint_update_expected_nodes 255%nat); vm_compute;reflexivity| |exact Step].
   intros site. cbn [joint_update_expr_416 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
   rewrite V415 V411 V414. unfold eval_type_of_expr; cbn [type_of_expr' eval_type_of_ref]; rewrite ?V415 ?V411 ?V414. destruct b0,b1,rest; reflexivity. }
 assert (V417 : VM.find 417 (history time) = Some (Gval (Fuint 1) [::false])).
 { rewrite (exception_stable_417_history inputs path history limit Boundary Steps time (S time) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)).
   eapply (reference_redirect_ground_step joint_update_node_offsets joint_update_expected_nodes 417 joint_update_expr_417);
   [exact joint_update_node_positions|exact joint_update_node_safety|apply (List.nth_error_In joint_update_expected_nodes 256%nat); vm_compute;reflexivity| |exact Step].
   intros site. cbn [joint_update_expr_417 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
   rewrite Mode. unfold eval_type_of_expr; cbn [type_of_expr' eval_type_of_ref]; rewrite ?Mode. destruct b0,b1,rest; reflexivity. }
 assert (V418 : VM.find 418 (history time) = Some (Gval (Fuint 1) [::b0 || b1])).
 { rewrite (exception_stable_418_history inputs path history limit Boundary Steps time (S time) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)).
   eapply (reference_redirect_ground_step joint_update_node_offsets joint_update_expected_nodes 418 joint_update_expr_418);
   [exact joint_update_node_positions|exact joint_update_node_safety|apply (List.nth_error_In joint_update_expected_nodes 257%nat); vm_compute;reflexivity| |exact Step].
   intros site. cbn [joint_update_expr_418 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
   rewrite V417 V412 V416. unfold eval_type_of_expr; cbn [type_of_expr' eval_type_of_ref]; rewrite ?V417 ?V412 ?V416. destruct b0,b1,rest; reflexivity. }
 exact V418.
Qed.
Theorem load_word_aligned_history inputs path history limit time b0 b1 rest :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 (65 <= time)%coq_nat -> (time < limit)%coq_nat ->
 VM.find 128 (history time) = Some (Gval (Fuint 1) [::false]) ->
 VM.find 126 (history time) = Some (Gval (Fuint 3) [::true;false;false]) ->
 VM.find 122 (history time) = Some (Gval (Fuint 32) (b0::b1::rest)) ->
 b0 = false /\ b1 = false.
Proof.
 intros Boundary Steps Lower Upper NoTrap Mode Address.
 destruct (dut_no_trap_invalid_flags_history inputs path history limit time Boundary Steps Lower Upper NoTrap) as [_ Zero].
 pose proof (load_word_invalid_history inputs path history limit time b0 b1 rest Boundary Steps Lower Upper Mode Address) as Invalid.
 specialize (Zero _ _ Invalid). cbn in Zero.
 apply Bool.orb_false_iff in Zero. exact Zero.
Qed.
Theorem load_half_invalid_history inputs path history limit time unsigned b0 b1 rest :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 (65 <= time)%coq_nat -> (time < limit)%coq_nat ->
 VM.find 126 (history time) = Some (Gval (Fuint 3) [::false;negb unsigned;unsigned]) ->
 VM.find 122 (history time) = Some (Gval (Fuint 32) (b0::b1::rest)) ->
 VM.find 418 (history time) = Some (Gval (Fuint 1) [::b0]).
Proof.
 intros Boundary Steps Lower Upper Mode Address.
 pose proof (Steps time Upper) as Step.
 assert (V409 : VM.find 409 (history time) = Some (Gval (Fuint 2) [::b0;b1])).
 { rewrite (exception_stable_409_history inputs path history limit Boundary Steps time (S time) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)).
   eapply (reference_redirect_ground_step joint_update_node_offsets joint_update_expected_nodes 409 joint_update_expr_409);
   [exact joint_update_node_positions|exact joint_update_node_safety|apply (List.nth_error_In joint_update_expected_nodes 248%nat); vm_compute;reflexivity| |exact Step].
   intros site. cbn [joint_update_expr_409 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
   rewrite Address. unfold eval_type_of_expr; cbn [type_of_expr' eval_type_of_ref]; rewrite ?Address. destruct unsigned,b0,b1,rest; reflexivity. }
 assert (V410 : VM.find 410 (history time) = Some (Gval (Fuint 1) [::b0 || b1])).
 { rewrite (exception_stable_410_history inputs path history limit Boundary Steps time (S time) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)).
   eapply (reference_redirect_ground_step joint_update_node_offsets joint_update_expected_nodes 410 joint_update_expr_410);
   [exact joint_update_node_positions|exact joint_update_node_safety|apply (List.nth_error_In joint_update_expected_nodes 249%nat); vm_compute;reflexivity| |exact Step].
   intros site. cbn [joint_update_expr_410 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
   rewrite V409. unfold eval_type_of_expr; cbn [type_of_expr' eval_type_of_ref]; rewrite ?V409. destruct unsigned,b0,b1,rest; reflexivity. }
 assert (V411 : VM.find 411 (history time) = Some (Gval (Fuint 1) [::b0])).
 { rewrite (exception_stable_411_history inputs path history limit Boundary Steps time (S time) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)).
   eapply (reference_redirect_ground_step joint_update_node_offsets joint_update_expected_nodes 411 joint_update_expr_411);
   [exact joint_update_node_positions|exact joint_update_node_safety|apply (List.nth_error_In joint_update_expected_nodes 250%nat); vm_compute;reflexivity| |exact Step].
   intros site. cbn [joint_update_expr_411 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
   rewrite Address. unfold eval_type_of_expr; cbn [type_of_expr' eval_type_of_ref]; rewrite ?Address. destruct unsigned,b0,b1,rest; reflexivity. }
 assert (V412 : VM.find 412 (history time) = Some (Gval (Fuint 1) [::b0])).
 { rewrite (exception_stable_412_history inputs path history limit Boundary Steps time (S time) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)).
   eapply (reference_redirect_ground_step joint_update_node_offsets joint_update_expected_nodes 412 joint_update_expr_412);
   [exact joint_update_node_positions|exact joint_update_node_safety|apply (List.nth_error_In joint_update_expected_nodes 251%nat); vm_compute;reflexivity| |exact Step].
   intros site. cbn [joint_update_expr_412 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
   rewrite Address. unfold eval_type_of_expr; cbn [type_of_expr' eval_type_of_ref]; rewrite ?Address. destruct unsigned,b0,b1,rest; reflexivity. }
 assert (V413 : VM.find 413 (history time) = Some (Gval (Fuint 1) [::false])).
 { rewrite (exception_stable_413_history inputs path history limit Boundary Steps time (S time) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)).
   eapply (reference_redirect_ground_step joint_update_node_offsets joint_update_expected_nodes 413 joint_update_expr_413);
   [exact joint_update_node_positions|exact joint_update_node_safety|apply (List.nth_error_In joint_update_expected_nodes 252%nat); vm_compute;reflexivity| |exact Step].
   intros site. cbn [joint_update_expr_413 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
   rewrite Mode. unfold eval_type_of_expr; cbn [type_of_expr' eval_type_of_ref]; rewrite ?Mode. destruct unsigned,b0,b1,rest; reflexivity. }
 assert (V414 : VM.find 414 (history time) = Some (Gval (Fuint 1) [::false])).
 { rewrite (exception_stable_414_history inputs path history limit Boundary Steps time (S time) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)).
   eapply (reference_redirect_ground_step joint_update_node_offsets joint_update_expected_nodes 414 joint_update_expr_414);
   [exact joint_update_node_positions|exact joint_update_node_safety|apply (List.nth_error_In joint_update_expected_nodes 253%nat); vm_compute;reflexivity| |exact Step].
   intros site. cbn [joint_update_expr_414 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
   rewrite V413 V410. unfold eval_type_of_expr; cbn [type_of_expr' eval_type_of_ref]; rewrite ?V413 ?V410. destruct unsigned,b0,b1,rest; reflexivity. }
 assert (V415 : VM.find 415 (history time) = Some (Gval (Fuint 1) [::negb unsigned])).
 { rewrite (exception_stable_415_history inputs path history limit Boundary Steps time (S time) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)).
   eapply (reference_redirect_ground_step joint_update_node_offsets joint_update_expected_nodes 415 joint_update_expr_415);
   [exact joint_update_node_positions|exact joint_update_node_safety|apply (List.nth_error_In joint_update_expected_nodes 254%nat); vm_compute;reflexivity| |exact Step].
   intros site. cbn [joint_update_expr_415 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
   rewrite Mode. unfold eval_type_of_expr; cbn [type_of_expr' eval_type_of_ref]; rewrite ?Mode. destruct unsigned,b0,b1,rest; reflexivity. }
 assert (V416 : VM.find 416 (history time) = Some (Gval (Fuint 1) [::b0 && negb unsigned])).
 { rewrite (exception_stable_416_history inputs path history limit Boundary Steps time (S time) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)).
   eapply (reference_redirect_ground_step joint_update_node_offsets joint_update_expected_nodes 416 joint_update_expr_416);
   [exact joint_update_node_positions|exact joint_update_node_safety|apply (List.nth_error_In joint_update_expected_nodes 255%nat); vm_compute;reflexivity| |exact Step].
   intros site. cbn [joint_update_expr_416 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
   rewrite V415 V411 V414. unfold eval_type_of_expr; cbn [type_of_expr' eval_type_of_ref]; rewrite ?V415 ?V411 ?V414. destruct unsigned,b0,b1,rest; reflexivity. }
 assert (V417 : VM.find 417 (history time) = Some (Gval (Fuint 1) [::unsigned])).
 { rewrite (exception_stable_417_history inputs path history limit Boundary Steps time (S time) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)).
   eapply (reference_redirect_ground_step joint_update_node_offsets joint_update_expected_nodes 417 joint_update_expr_417);
   [exact joint_update_node_positions|exact joint_update_node_safety|apply (List.nth_error_In joint_update_expected_nodes 256%nat); vm_compute;reflexivity| |exact Step].
   intros site. cbn [joint_update_expr_417 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
   rewrite Mode. unfold eval_type_of_expr; cbn [type_of_expr' eval_type_of_ref]; rewrite ?Mode. destruct unsigned,b0,b1,rest; reflexivity. }
 assert (V418 : VM.find 418 (history time) = Some (Gval (Fuint 1) [::b0])).
 { rewrite (exception_stable_418_history inputs path history limit Boundary Steps time (S time) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)).
   eapply (reference_redirect_ground_step joint_update_node_offsets joint_update_expected_nodes 418 joint_update_expr_418);
   [exact joint_update_node_positions|exact joint_update_node_safety|apply (List.nth_error_In joint_update_expected_nodes 257%nat); vm_compute;reflexivity| |exact Step].
   intros site. cbn [joint_update_expr_418 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
   rewrite V417 V412 V416. unfold eval_type_of_expr; cbn [type_of_expr' eval_type_of_ref]; rewrite ?V417 ?V412 ?V416. destruct unsigned,b0,b1,rest; reflexivity. }
 exact V418.
Qed.

(* Observed load alignment. *)
Require Import FormalLocalHistory FormalDeclaredConnection JointUpdateConnectionCertificates DUTRedirectDecode.
Theorem load_word_aligned_observed memory inputs k observed b0 b1 rest :
 generated_observe memory inputs k = Some observed -> generated_legal_trace memory inputs k ->
 VM.find 1 (formal_external_inputs (generated_observation_input inputs k)) = Some (Gval (Fuint 1) [::false]) ->
 size (b0::b1::rest) = 32%nat ->
 VM.find 7755 (top_environment observed) = Some (Gval (Fuint 3) [::true;false;false]) ->
 VM.find 7752 (top_environment observed) = Some (Gval (Fuint 32) (b0::b1::rest)) ->
 b0 = false /\ b1 = false.
Proof.
 intros Observe Legal Reset Size Mode Target.
 destruct (dut_no_trap_observed_context memory inputs k observed Observe Legal Reset)
 as [history [Last [Boundary [Steps NoTrap]]]].
 assert (TargetEarlier : VM.find 7752 (history 9257%nat) = Some (Gval (Fuint 32) (b0::b1::rest))).
 { rewrite (exception_stable_7752_history (generated_observation_input inputs k) nil history 9259 Boundary Steps 9257 9259 ltac:(vm_compute;lia) ltac:(vm_compute;lia) ltac:(vm_compute;lia) (le_n 9259)) Last. exact Target. }
 assert (ModeEarlier : VM.find 7755 (history 9257%nat) = Some (Gval (Fuint 3) [::true;false;false])).
 { rewrite (exception_stable_7755_history (generated_observation_input inputs k) nil history 9259 Boundary Steps 9257 9259 ltac:(vm_compute;lia) ltac:(vm_compute;lia) ltac:(vm_compute;lia) (le_n 9259)) Last. exact Mode. }
 assert (Address : VM.find 122 (history 9258%nat) = Some (Gval (Fuint 32) (b0::b1::rest))).
 { eapply (declared_connection_value 99 flat_statements joint_update_connection_122_decl joint_update_connection_122_mid joint_update_connection_122_tail 122 7752 32 (Gval (Fuint 32) (b0::b1::rest)));
 [exact joint_update_connection_122_position|exact joint_update_connection_122_split|exact joint_update_connection_122_straight|exact joint_update_connection_122_mid_safe|exact joint_update_connection_122_tail_safe|exact joint_update_connection_122_nonregister|reflexivity|exact TargetEarlier|apply dut_decode_adapt; exact Size|apply Steps; vm_compute;lia]. }
 assert (Kind : VM.find 126 (history 9258%nat) = Some (Gval (Fuint 3) [::true;false;false])).
 { eapply (declared_connection_value 103 flat_statements joint_update_connection_126_decl joint_update_connection_126_mid joint_update_connection_126_tail 126 7755 3 (Gval (Fuint 3) [::true;false;false]));
 [exact joint_update_connection_126_position|exact joint_update_connection_126_split|exact joint_update_connection_126_straight|exact joint_update_connection_126_mid_safe|exact joint_update_connection_126_tail_safe|exact joint_update_connection_126_nonregister|reflexivity|exact ModeEarlier|reflexivity|apply Steps; vm_compute;lia]. }
 exact (load_word_aligned_history (generated_observation_input inputs k) nil history 9259 9258 b0 b1 rest Boundary Steps ltac:(vm_compute;lia) ltac:(vm_compute;lia)
 (NoTrap 9258 ltac:(vm_compute;lia) ltac:(vm_compute;lia)) Kind Address).
Qed.
Theorem load_half_aligned_observed memory inputs k observed unsigned b0 b1 rest :
 generated_observe memory inputs k = Some observed -> generated_legal_trace memory inputs k ->
 VM.find 1 (formal_external_inputs (generated_observation_input inputs k)) = Some (Gval (Fuint 1) [::false]) ->
 size (b0::b1::rest) = 32%nat ->
 VM.find 7755 (top_environment observed) = Some (Gval (Fuint 3) [::false;negb unsigned;unsigned]) ->
 VM.find 7752 (top_environment observed) = Some (Gval (Fuint 32) (b0::b1::rest)) ->
 b0 = false.
Proof.
 intros Observe Legal Reset Size Mode Target.
 destruct (dut_no_trap_observed_context memory inputs k observed Observe Legal Reset)
 as [history [Last [Boundary [Steps NoTrap]]]].
 assert (TargetEarlier : VM.find 7752 (history 9257%nat) = Some (Gval (Fuint 32) (b0::b1::rest))).
 { rewrite (exception_stable_7752_history (generated_observation_input inputs k) nil history 9259 Boundary Steps 9257 9259 ltac:(vm_compute;lia) ltac:(vm_compute;lia) ltac:(vm_compute;lia) (le_n 9259)) Last. exact Target. }
 assert (ModeEarlier : VM.find 7755 (history 9257%nat) = Some (Gval (Fuint 3) [::false;negb unsigned;unsigned])).
 { rewrite (exception_stable_7755_history (generated_observation_input inputs k) nil history 9259 Boundary Steps 9257 9259 ltac:(vm_compute;lia) ltac:(vm_compute;lia) ltac:(vm_compute;lia) (le_n 9259)) Last. exact Mode. }
 assert (Address : VM.find 122 (history 9258%nat) = Some (Gval (Fuint 32) (b0::b1::rest))).
 { eapply (declared_connection_value 99 flat_statements joint_update_connection_122_decl joint_update_connection_122_mid joint_update_connection_122_tail 122 7752 32 (Gval (Fuint 32) (b0::b1::rest)));
 [exact joint_update_connection_122_position|exact joint_update_connection_122_split|exact joint_update_connection_122_straight|exact joint_update_connection_122_mid_safe|exact joint_update_connection_122_tail_safe|exact joint_update_connection_122_nonregister|reflexivity|exact TargetEarlier|apply dut_decode_adapt; exact Size|apply Steps; vm_compute;lia]. }
 assert (Kind : VM.find 126 (history 9258%nat) = Some (Gval (Fuint 3) [::false;negb unsigned;unsigned])).
 { eapply (declared_connection_value 103 flat_statements joint_update_connection_126_decl joint_update_connection_126_mid joint_update_connection_126_tail 126 7755 3 (Gval (Fuint 3) [::false;negb unsigned;unsigned]));
 [exact joint_update_connection_126_position|exact joint_update_connection_126_split|exact joint_update_connection_126_straight|exact joint_update_connection_126_mid_safe|exact joint_update_connection_126_tail_safe|exact joint_update_connection_126_nonregister|reflexivity|exact ModeEarlier|destruct unsigned;reflexivity|apply Steps; vm_compute;lia]. }
 destruct (dut_no_trap_invalid_flags_history (generated_observation_input inputs k) nil history 9259 9258 Boundary Steps ltac:(vm_compute;lia) ltac:(vm_compute;lia)
 (NoTrap 9258 ltac:(vm_compute;lia) ltac:(vm_compute;lia))) as [_ Zero].
 pose proof (load_half_invalid_history (generated_observation_input inputs k) nil history 9259 9258 unsigned b0 b1 rest Boundary Steps ltac:(vm_compute;lia) ltac:(vm_compute;lia) Kind Address) as Invalid.
 exact (Zero _ _ Invalid).
Qed.
