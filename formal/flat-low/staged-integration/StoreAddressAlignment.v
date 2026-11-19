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
Require Import FormalExceptionInput JointUpdateConnectionCertificates FormalDeclaredConnection DUTRedirectDecode.
Theorem dut_no_trap_store_invalid_history inputs path history limit time :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 (65 <= time)%coq_nat -> (time < limit)%coq_nat ->
 VM.find 128 (history time) = Some (Gval (Fuint 1) [::false]) ->
 dut_node_low_zero 425 (history time).
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
 destruct (dut_or_low_recover 440 437 439 _ (history time) (history time) (history (S time))
  ltac:(apply (List.nth_error_In joint_update_expected_nodes 279%nat); vm_compute; reflexivity)
  (exception_concrete_437_history inputs path history limit Boundary Steps time ltac:(lia) ltac:(lia))
  (exception_concrete_439_history inputs path history limit Boundary Steps time ltac:(lia) ltac:(lia))
  (exception_stable_440_history inputs path history limit Boundary Steps time (S time) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) Zero440 Step)
  as [Zero437 Zero439].
 destruct (dut_or_low_recover 437 435 436 _ (history time) (history time) (history (S time))
  ltac:(apply (List.nth_error_In joint_update_expected_nodes 276%nat); vm_compute; reflexivity)
  (exception_concrete_435_history inputs path history limit Boundary Steps time ltac:(lia) ltac:(lia))
  (exception_concrete_436_history inputs path history limit Boundary Steps time ltac:(lia) ltac:(lia))
  (exception_stable_437_history inputs path history limit Boundary Steps time (S time) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) Zero437 Step)
  as [Zero435 Zero436].
 destruct (dut_or_low_recover 435 428 434 _ (history time) (history time) (history (S time))
  ltac:(apply (List.nth_error_In joint_update_expected_nodes 274%nat); vm_compute; reflexivity)
  (exception_concrete_428_history inputs path history limit Boundary Steps time ltac:(lia) ltac:(lia))
  (exception_concrete_434_history inputs path history limit Boundary Steps time ltac:(lia) ltac:(lia))
  (exception_stable_435_history inputs path history limit Boundary Steps time (S time) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) Zero435 Step)
  as [Zero428 Zero434].
 destruct (dut_or_low_recover 428 427 425 _ (history time) (history time) (history (S time))
  ltac:(apply (List.nth_error_In joint_update_expected_nodes 267%nat); vm_compute; reflexivity)
  (exception_concrete_427_history inputs path history limit Boundary Steps time ltac:(lia) ltac:(lia))
  (exception_concrete_425_history inputs path history limit Boundary Steps time ltac:(lia) ltac:(lia))
  (exception_stable_428_history inputs path history limit Boundary Steps time (S time) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) Zero428 Step)
  as [Zero427 Zero425].
 exact Zero425.
Qed.
Theorem store_invalid_history inputs path history limit time half b0 b1 rest :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 (65 <= time)%coq_nat -> (time < limit)%coq_nat ->
 VM.find 125 (history time) = Some (Gval (Fuint 2) [::negb half;half]) ->
 VM.find 122 (history time) = Some (Gval (Fuint 32) (b0::b1::rest)) ->
 VM.find 425 (history time) = Some (Gval (Fuint 1) [::b0 || (b1 && negb half)]).
Proof.
 intros Boundary Steps Lower Upper Mode Address.
 pose proof (Steps time Upper) as Step.
 assert (V419 : VM.find 419 (history time) = Some (Gval (Fuint 2) [::b0;b1])).
 { rewrite (exception_stable_419_history inputs path history limit Boundary Steps time (S time) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)).
 eapply (reference_redirect_ground_step joint_update_node_offsets joint_update_expected_nodes 419 joint_update_expr_419);
 [exact joint_update_node_positions|exact joint_update_node_safety|apply (List.nth_error_In joint_update_expected_nodes 258%nat);vm_compute;reflexivity| |exact Step].
 intros site. cbn [joint_update_expr_419 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
 rewrite Address. unfold eval_type_of_expr;cbn [type_of_expr' eval_type_of_ref];rewrite ?Address. destruct half,b0,b1,rest;reflexivity. }
 assert (V420 : VM.find 420 (history time) = Some (Gval (Fuint 1) [::b0 || b1])).
 { rewrite (exception_stable_420_history inputs path history limit Boundary Steps time (S time) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)).
 eapply (reference_redirect_ground_step joint_update_node_offsets joint_update_expected_nodes 420 joint_update_expr_420);
 [exact joint_update_node_positions|exact joint_update_node_safety|apply (List.nth_error_In joint_update_expected_nodes 259%nat);vm_compute;reflexivity| |exact Step].
 intros site. cbn [joint_update_expr_420 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
 rewrite V419. unfold eval_type_of_expr;cbn [type_of_expr' eval_type_of_ref];rewrite ?V419. destruct half,b0,b1,rest;reflexivity. }
 assert (V421 : VM.find 421 (history time) = Some (Gval (Fuint 1) [::b0])).
 { rewrite (exception_stable_421_history inputs path history limit Boundary Steps time (S time) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)).
 eapply (reference_redirect_ground_step joint_update_node_offsets joint_update_expected_nodes 421 joint_update_expr_421);
 [exact joint_update_node_positions|exact joint_update_node_safety|apply (List.nth_error_In joint_update_expected_nodes 260%nat);vm_compute;reflexivity| |exact Step].
 intros site. cbn [joint_update_expr_421 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
 rewrite Address. unfold eval_type_of_expr;cbn [type_of_expr' eval_type_of_ref];rewrite ?Address. destruct half,b0,b1,rest;reflexivity. }
 assert (V422 : VM.find 422 (history time) = Some (Gval (Fuint 1) [::negb half])).
 { rewrite (exception_stable_422_history inputs path history limit Boundary Steps time (S time) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)).
 eapply (reference_redirect_ground_step joint_update_node_offsets joint_update_expected_nodes 422 joint_update_expr_422);
 [exact joint_update_node_positions|exact joint_update_node_safety|apply (List.nth_error_In joint_update_expected_nodes 261%nat);vm_compute;reflexivity| |exact Step].
 intros site. cbn [joint_update_expr_422 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
 rewrite Mode. unfold eval_type_of_expr;cbn [type_of_expr' eval_type_of_ref];rewrite ?Mode. destruct half,b0,b1,rest;reflexivity. }
 assert (V423 : VM.find 423 (history time) = Some (Gval (Fuint 1) [::(b0 || b1) && negb half])).
 { rewrite (exception_stable_423_history inputs path history limit Boundary Steps time (S time) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)).
 eapply (reference_redirect_ground_step joint_update_node_offsets joint_update_expected_nodes 423 joint_update_expr_423);
 [exact joint_update_node_positions|exact joint_update_node_safety|apply (List.nth_error_In joint_update_expected_nodes 262%nat);vm_compute;reflexivity| |exact Step].
 intros site. cbn [joint_update_expr_423 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
 rewrite V422 V420. unfold eval_type_of_expr;cbn [type_of_expr' eval_type_of_ref];rewrite ?V422 ?V420. destruct half,b0,b1,rest;reflexivity. }
 assert (V424 : VM.find 424 (history time) = Some (Gval (Fuint 1) [::half])).
 { rewrite (exception_stable_424_history inputs path history limit Boundary Steps time (S time) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)).
 eapply (reference_redirect_ground_step joint_update_node_offsets joint_update_expected_nodes 424 joint_update_expr_424);
 [exact joint_update_node_positions|exact joint_update_node_safety|apply (List.nth_error_In joint_update_expected_nodes 263%nat);vm_compute;reflexivity| |exact Step].
 intros site. cbn [joint_update_expr_424 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
 rewrite Mode. unfold eval_type_of_expr;cbn [type_of_expr' eval_type_of_ref];rewrite ?Mode. destruct half,b0,b1,rest;reflexivity. }
 assert (V425 : VM.find 425 (history time) = Some (Gval (Fuint 1) [::b0 || (b1 && negb half)])).
 { rewrite (exception_stable_425_history inputs path history limit Boundary Steps time (S time) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)).
 eapply (reference_redirect_ground_step joint_update_node_offsets joint_update_expected_nodes 425 joint_update_expr_425);
 [exact joint_update_node_positions|exact joint_update_node_safety|apply (List.nth_error_In joint_update_expected_nodes 264%nat);vm_compute;reflexivity| |exact Step].
 intros site. cbn [joint_update_expr_425 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
 rewrite V424 V421 V423. unfold eval_type_of_expr;cbn [type_of_expr' eval_type_of_ref];rewrite ?V424 ?V421 ?V423. destruct half,b0,b1,rest;reflexivity. }
 exact V425.
Qed.
Theorem store_aligned_history inputs path history limit time half b0 b1 rest :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 (65 <= time)%coq_nat -> (time < limit)%coq_nat ->
 VM.find 128 (history time) = Some (Gval (Fuint 1) [::false]) ->
 VM.find 125 (history time) = Some (Gval (Fuint 2) [::negb half;half]) ->
 VM.find 122 (history time) = Some (Gval (Fuint 32) (b0::b1::rest)) ->
 b0 = false /\ (half = false -> b1 = false).
Proof.
 intros Boundary Steps Lower Upper NoTrap Mode Address.
 pose proof (dut_no_trap_store_invalid_history inputs path history limit time Boundary Steps Lower Upper NoTrap) as Zero.
 pose proof (store_invalid_history inputs path history limit time half b0 b1 rest Boundary Steps Lower Upper Mode Address) as Invalid.
 specialize (Zero _ _ Invalid). cbn in Zero. destruct half,b0,b1;cbn in Zero;try discriminate;auto.
Qed.
(* Observed store alignment. *)
Require Import FormalLocalHistory.
Theorem store_aligned_observed memory inputs k observed half b0 b1 rest :
 generated_observe memory inputs k = Some observed -> generated_legal_trace memory inputs k ->
 VM.find 1 (formal_external_inputs (generated_observation_input inputs k)) = Some (Gval (Fuint 1) [::false]) ->
 size (b0::b1::rest) = 32%nat ->
 VM.find 7754 (top_environment observed) = Some (Gval (Fuint 2) [::negb half;half]) ->
 VM.find 7752 (top_environment observed) = Some (Gval (Fuint 32) (b0::b1::rest)) ->
 b0 = false /\ (half = false -> b1 = false).
Proof.
 intros Observe Legal Reset Size Mode Target.
 destruct (dut_no_trap_observed_context memory inputs k observed Observe Legal Reset)
 as [history [Last [Boundary [Steps NoTrap]]]].
 assert (TargetEarlier : VM.find 7752 (history 9257%nat) = Some (Gval (Fuint 32) (b0::b1::rest))).
 { rewrite (exception_stable_7752_history (generated_observation_input inputs k) nil history 9259 Boundary Steps 9257 9259 ltac:(vm_compute;lia) ltac:(vm_compute;lia) ltac:(vm_compute;lia) (le_n 9259)) Last. exact Target. }
 assert (ModeEarlier : VM.find 7754 (history 9257%nat) = Some (Gval (Fuint 2) [::negb half;half])).
 { rewrite (exception_stable_7754_history (generated_observation_input inputs k) nil history 9259 Boundary Steps 9257 9259 ltac:(vm_compute;lia) ltac:(vm_compute;lia) ltac:(vm_compute;lia) (le_n 9259)) Last. exact Mode. }
 assert (Address : VM.find 122 (history 9258%nat) = Some (Gval (Fuint 32) (b0::b1::rest))).
 { eapply (declared_connection_value 99 flat_statements joint_update_connection_122_decl joint_update_connection_122_mid joint_update_connection_122_tail 122 7752 32 (Gval (Fuint 32) (b0::b1::rest)));
 [exact joint_update_connection_122_position|exact joint_update_connection_122_split|exact joint_update_connection_122_straight|exact joint_update_connection_122_mid_safe|exact joint_update_connection_122_tail_safe|exact joint_update_connection_122_nonregister|reflexivity|exact TargetEarlier|apply dut_decode_adapt; exact Size|apply Steps; vm_compute;lia]. }
 assert (Kind : VM.find 125 (history 9258%nat) = Some (Gval (Fuint 2) [::negb half;half])).
 { eapply (declared_connection_value 102 flat_statements joint_update_connection_125_decl joint_update_connection_125_mid joint_update_connection_125_tail 125 7754 2 (Gval (Fuint 2) [::negb half;half]));
 [exact joint_update_connection_125_position|exact joint_update_connection_125_split|exact joint_update_connection_125_straight|exact joint_update_connection_125_mid_safe|exact joint_update_connection_125_tail_safe|exact joint_update_connection_125_nonregister|reflexivity|exact ModeEarlier|destruct half;reflexivity|apply Steps; vm_compute;lia]. }
 exact (store_aligned_history (generated_observation_input inputs k) nil history 9259 9258 half b0 b1 rest Boundary Steps ltac:(vm_compute;lia) ltac:(vm_compute;lia)
 (NoTrap 9258 ltac:(vm_compute;lia) ltac:(vm_compute;lia)) Kind Address).
Qed.
