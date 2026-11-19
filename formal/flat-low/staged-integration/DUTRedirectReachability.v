Require Import DUTRedirectDecode DUTRedirectSemantics ReferenceRedirectSemantics
 DelayedDUTRedirectSemantics ObservedAssertion43CommitValid Assertion43Enable
 CoreSocModel ComparisonNodes FormalLocalHistory.
From Coq Require Import NArith ZArith Lia List.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From nbits Require Import NBitsDef NBitsOp.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths
 Firrtl_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Local Opaque flat_statements flat_memories generated_modules generated_top.
(* The comparison's real enable implies checker commit-valid; it need not be
   assumed separately. Bubble/reset observations are not globally enabled. *)
Theorem delayed_assertion43_redirect_observed memory inputs k observed committed next_observed
 instruction dut_left dut_right kind selector ref_left ref_right immediate pc csr :
 generated_observe memory inputs k = Some observed ->
 generated_run memory inputs (S k) = Some committed ->
 generated_observe memory inputs (S k) = Some next_observed ->
 generated_legal_trace memory inputs (S k) ->
 VM.find 1 (formal_external_inputs (generated_observation_input inputs k)) = Some (Gval (Fuint 1) [::false]) ->
 generated_legal_trace memory inputs k ->
 VM.find 1357 (top_environment observed) = Some (Gval (Fuint 32) dut_left) ->
 VM.find 1358 (top_environment observed) = Some (Gval (Fuint 32) dut_right) ->
 VM.find 1359 (top_environment observed) = Some (Gval (Fuint 3) kind) ->
 VM.find 84 (top_environment observed) = Some (Gval (Fuint 2) selector) ->
 VM.find 7748 (top_environment observed) = Some (Gval (Fuint 32) instruction) ->
 generated_expr_true assertion43_enable (top_environment next_observed) ->
 size instruction = 32%nat ->
 VM.find 2209 (top_environment next_observed) = Some (Gval (Fuint 32) ref_left) ->
 VM.find 2804 (top_environment next_observed) = Some (Gval (Fuint 32) ref_right) ->
 VM.find 2552 (top_environment next_observed) = Some (Gval (Fuint 32) immediate) ->
 VM.find 7331 (top_environment next_observed) = Some (Gval (Fuint 32) pc) ->
 VM.find 7332 (top_environment next_observed) = Some (Gval (Fuint 32) csr) ->
 size dut_left = 32%nat -> size dut_right = 32%nat ->
 size ref_left = 32%nat -> size ref_right = 32%nat -> size pc = 32%nat -> size csr = 32%nat ->
 dut_operand_tests_match (to_N kind) (to_N dut_left) (to_N dut_right) (to_N ref_left) (to_N ref_right) ->
 (dut_reference_taken (to_N instruction) (to_N ref_left) (to_N ref_right) = true ->
  reference_redirect_aligned (N.testbit (to_N csr) 2) (to_N pc + to_N immediate) = true) ->
 (N.eqb (N.land (to_N instruction) 28799) 103 = true ->
  reference_redirect_aligned (N.testbit (to_N csr) 2) (N.clearbit (to_N ref_left + to_N immediate) 0) = true) ->
 VM.find 7760 (top_environment next_observed) = VM.find 6507 (top_environment next_observed).
Proof.
 intros Observe Run NextObserve NextLegal Reset Legal DutLeft DutRight Kind Selector Front Enabled InstructionSize RefLeft RefRight Immediate Pc Csr
 DutLeftSize DutRightSize RefLeftSize RefRightSize PcSize CsrSize Operands BranchAligned JalrAligned.
 pose proof (observed_assertion43_commit_valid memory inputs (S k) next_observed NextObserve NextLegal Enabled) as CommitValid.
 exact (delayed_decoded_reference_redirect_observed memory inputs k observed committed next_observed instruction dut_left dut_right kind selector ref_left ref_right immediate pc csr Observe Run NextObserve NextLegal Reset Legal DutLeft DutRight Kind Selector Front CommitValid InstructionSize RefLeft RefRight Immediate Pc Csr DutLeftSize DutRightSize RefLeftSize RefRightSize PcSize CsrSize Operands BranchAligned JalrAligned).
Qed.
Require Import ReferenceRedirectSpine JointUpdateNodePositions JointUpdateExpressionCertificates
 ExceptionStabilityHistory JointBoundaryRegisters ConcreteRegisterInitialization
 FormalDeclaredConnection FormalExceptionInput JointUpdateConnectionCertificates.
Definition dut_node_low_zero node env := forall width bits,
 VM.find node env = Some (Gval (Fuint width) bits) -> nth false bits 0 = false.
Lemma dut_or_low left right : nth false (orB left right) 0 = (nth false left 0 || nth false right 0).
Proof. destruct left as [|a left], right as [|b right]; try destruct a; try destruct b; reflexivity. Qed.
Lemma dut_or_eval lw rw left right :
 eval_binop Bor (Gval (Fuint lw) left) (Gval (Fuint rw) right) = Some (Gval (Fuint (maxn lw rw)) (orB left right)).
Proof.
 unfold eval_binop. cbn [eval_binop_basic].
 destruct (absorbing_bit Bor (Gval (Fuint lw) left) (Gval (Fuint rw) right)); reflexivity.
Qed.
Lemma dut_or_low_recover node left right invalid old current result :
 List.In (node,@Eprim_binop VarOrder.T Bor (@Eref VarOrder.T (@Eid VarOrder.T left)) (@Eref VarOrder.T (@Eid VarOrder.T right))) joint_update_expected_nodes ->
 (exists width bits, VM.find left old = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find right old = Some (Gval (Fuint width) bits)) ->
 VM.find node old = VM.find node result ->
 dut_node_low_zero node old ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 dut_node_low_zero left old /\ dut_node_low_zero right old.
Proof.
 intros Member [lw [lb Left]] [rw [rb Right]] Stable Zero Step.
 assert (Output : VM.find node result = Some (Gval (Fuint (maxn lw rw)) (orB lb rb))).
 { eapply (reference_redirect_ground_step joint_update_node_offsets joint_update_expected_nodes node _);
   [exact joint_update_node_positions|exact joint_update_node_safety|exact Member| |exact Step].
   intros site. cbn [eval_hfexpr_validif_policy eval_href_validif_policy]. rewrite Left Right. apply dut_or_eval. }
 rewrite <- Stable in Output. specialize (Zero _ _ Output). rewrite dut_or_low in Zero. apply Bool.orb_false_iff in Zero.
 unfold dut_node_low_zero. split; intros width bits Lookup.
 - rewrite Left in Lookup. inversion Lookup; subst bits. exact (proj1 Zero).
 - rewrite Right in Lookup. inversion Lookup; subst bits. exact (proj2 Zero).
Qed.
Lemma dut_adapt_low width bits :
 adapt_hvalue_as_type (Gval (Fuint width) bits) (Gtyp (Fuint 1)) = Some (Gval (Fuint 1) [::nth false bits 0]).
Proof. destruct bits as [|b bits]; [reflexivity|]. cbn [adapt_hvalue_as_type take]. rewrite take0. destruct b; reflexivity. Qed.

(* CSR.scala iaddrInvalid = pc_check && addr(1). The OR tree is recovered
   from actual successful steps; other exception inputs remain unrestricted. *)
Theorem dut_no_trap_invalid_flags_history inputs path history limit time :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 (65 <= time)%coq_nat -> (time < limit)%coq_nat ->
 VM.find 128 (history time) = Some (Gval (Fuint 1) [::false]) ->
 dut_node_low_zero 408 (history time) /\ dut_node_low_zero 418 (history time).
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
 destruct (dut_or_low_recover 427 426 418 _ (history time) (history time) (history (S time))
  ltac:(apply (List.nth_error_In joint_update_expected_nodes 266%nat); vm_compute; reflexivity)
  (exception_concrete_426_history inputs path history limit Boundary Steps time ltac:(lia) ltac:(lia))
  (exception_concrete_418_history inputs path history limit Boundary Steps time ltac:(lia) ltac:(lia))
  (exception_stable_427_history inputs path history limit Boundary Steps time (S time) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) Zero427 Step)
  as [Zero426 Zero418].
 destruct (dut_or_low_recover 426 124 408 _ (history time) (history time) (history (S time))
  ltac:(apply (List.nth_error_In joint_update_expected_nodes 265%nat); vm_compute; reflexivity)
  (exception_concrete_124_history inputs path history limit Boundary Steps time ltac:(lia) ltac:(lia))
  (exception_concrete_408_history inputs path history limit Boundary Steps time ltac:(lia) ltac:(lia))
  (exception_stable_426_history inputs path history limit Boundary Steps time (S time) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) Zero426 Step)
  as [Zero124 Zero408].
 split; assumption.
Qed.
Theorem dut_no_trap_target_bit_history inputs path history limit time target :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 (65 <= time)%coq_nat -> (time < limit)%coq_nat ->
 VM.find 128 (history time) = Some (Gval (Fuint 1) [::false]) ->
 VM.find 127 (history time) = Some (Gval (Fuint 1) [::true]) ->
 VM.find 122 (history time) = Some (Gval (Fuint 32) target) ->
 nth false target 1 = false.
Proof.
 intros Boundary Steps Lower Upper NoTrap Redirect Target.
 pose proof (Steps time Upper) as Step.
 destruct (dut_no_trap_invalid_flags_history inputs path history limit time Boundary Steps Lower Upper NoTrap) as [Zero408 Zero418].
 assert (Bit : VM.find 407 (history time) = Some (Gval (Fuint 1) (drop 1 (take 2 target)))).
 { rewrite (exception_stable_407_history inputs path history limit Boundary Steps time (S time) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)).
   eapply (reference_redirect_ground_step joint_update_node_offsets joint_update_expected_nodes 407 joint_update_expr_407);
   [exact joint_update_node_positions|exact joint_update_node_safety|apply (List.nth_error_In joint_update_expected_nodes 246%nat); vm_compute; reflexivity| |exact Step].
   intros site. cbn [joint_update_expr_407 eval_hfexpr_validif_policy eval_href_validif_policy]. rewrite Target. reflexivity. }
 assert (Invalid : VM.find 408 (history time) = Some (Gval (Fuint 1) (andB [::true] (drop 1 (take 2 target))))).
 { rewrite (exception_stable_408_history inputs path history limit Boundary Steps time (S time) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)).
   eapply (reference_redirect_ground_step joint_update_node_offsets joint_update_expected_nodes 408 joint_update_expr_408);
   [exact joint_update_node_positions|exact joint_update_node_safety|apply (List.nth_error_In joint_update_expected_nodes 247%nat); vm_compute; reflexivity| |exact Step].
   intros site. cbn [joint_update_expr_408 eval_hfexpr_validif_policy eval_href_validif_policy]. rewrite Redirect Bit.
   unfold eval_binop. cbn [eval_binop_basic]. destruct (absorbing_bit Band (Gval (Fuint 1) [::true]) (Gval (Fuint 1) (drop 1 (take 2 target)))); reflexivity. }
 specialize (Zero408 _ _ Invalid).
 destruct target as [|a [|b rest]]; cbn in Zero408 |- *; try reflexivity.
 exact Zero408.
Qed.
Require Import ObservedLegalNoTrap ExceptionSourceNoTrap JointBoundaryReachable
 JointBoundaryPreparation FormalFetchType.
Theorem dut_no_trap_observed_context memory inputs k observed :
 generated_observe memory inputs k = Some observed ->
 generated_legal_trace memory inputs k ->
 VM.find 1 (formal_external_inputs (generated_observation_input inputs k)) = Some (Gval (Fuint 1) [::false]) ->
 exists history,
 history 9259%nat = top_environment observed /\
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) /\
 (forall i, (i < 9259)%coq_nat -> formal_value_iter (formal_invalid_policy (generated_observation_input inputs k) nil) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) /\
 (forall time, (41 <= time)%coq_nat -> (time <= 9259)%coq_nat -> VM.find 128 (history time) = Some (Gval (Fuint 1) [::false])).
Proof.
 intros Observe Legal Reset.
 destruct (observed_legal_no_trap_history memory inputs k observed Observe Legal Reset)
 as [committed [initial [history [Run [Prepare [First [Last [Steps NoTrap]]]]]]]].
 destruct (fetch9220_run_type memory inputs k committed Run) as [env [value [Env Rest]]].
 destruct (joint_boundary_reachable memory inputs k committed Run Legal) as [Registers Storage].
 unfold top_environment in Registers. rewrite Env in Registers.
 assert (Boundary : forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)).
 { intros node width Member. rewrite First.
   exact (joint_boundary_prepared_concrete committed env _ initial node width Member (Registers node width Member) Env Prepare). }
 exists history. split; [exact Last|]. split; [exact Boundary|]. split; [exact Steps|].
 exact (exception_source_false_after_settling (generated_observation_input inputs k) nil history Boundary Steps NoTrap).
Qed.
Theorem dut_no_trap_target_bit_observed memory inputs k observed target :
 generated_observe memory inputs k = Some observed ->
 generated_legal_trace memory inputs k ->
 VM.find 1 (formal_external_inputs (generated_observation_input inputs k)) = Some (Gval (Fuint 1) [::false]) ->
 VM.find 7760 (top_environment observed) = Some (Gval (Fuint 1) [::true]) ->
 VM.find 7752 (top_environment observed) = Some (Gval (Fuint 32) target) ->
 size target = 32%nat ->
 N.testbit (to_N target) 1 = false.
Proof.
 intros Observe Legal Reset Redirect Target Size.
 destruct (dut_no_trap_observed_context memory inputs k observed Observe Legal Reset)
 as [history [Last [Boundary [Steps NoTrap]]]].
 assert (TargetEarlier : VM.find 7752 (history 9257%nat) = Some (Gval (Fuint 32) target)).
 { rewrite (exception_stable_7752_history (generated_observation_input inputs k) nil history 9259 Boundary Steps 9257 9259 ltac:(vm_compute;lia) ltac:(vm_compute;lia) ltac:(vm_compute;lia) (le_n 9259)) Last. exact Target. }
 assert (RedirectEarlier : VM.find 7760 (history 9257%nat) = Some (Gval (Fuint 1) [::true])).
 { rewrite (exception_stable_7760_history (generated_observation_input inputs k) nil history 9259 Boundary Steps 9257 9259 ltac:(vm_compute;lia) ltac:(vm_compute;lia) ltac:(vm_compute;lia) (le_n 9259)) Last. exact Redirect. }
 assert (Address : VM.find 122 (history 9258%nat) = Some (Gval (Fuint 32) target)).
 { eapply (declared_connection_value 99 flat_statements joint_update_connection_122_decl joint_update_connection_122_mid joint_update_connection_122_tail 122 7752 32 (Gval (Fuint 32) target));
   [exact joint_update_connection_122_position|exact joint_update_connection_122_split|exact joint_update_connection_122_straight|exact joint_update_connection_122_mid_safe|exact joint_update_connection_122_tail_safe|exact joint_update_connection_122_nonregister|reflexivity|exact TargetEarlier|apply dut_decode_adapt; exact Size|apply Steps; vm_compute;lia]. }
 assert (Check : VM.find 127 (history 9258%nat) = Some (Gval (Fuint 1) [::true])).
 { eapply (declared_connection_value 104 flat_statements joint_update_connection_127_decl joint_update_connection_127_mid joint_update_connection_127_tail 127 7760 1 (Gval (Fuint 1) [::true]));
   [exact joint_update_connection_127_position|exact joint_update_connection_127_split|exact joint_update_connection_127_straight|exact joint_update_connection_127_mid_safe|exact joint_update_connection_127_tail_safe|exact joint_update_connection_127_nonregister|reflexivity|exact RedirectEarlier|reflexivity|apply Steps; vm_compute;lia]. }
 rewrite (redirect_to_N_testbit target 1).
 exact (dut_no_trap_target_bit_history (generated_observation_input inputs k) nil history 9259 9258 target Boundary Steps ltac:(vm_compute;lia) ltac:(vm_compute;lia)
   (NoTrap 9258 ltac:(vm_compute;lia) ltac:(vm_compute;lia)) Check Address).
Qed.

Theorem dut_no_trap_invalid_flags_observed memory inputs k observed :
 generated_observe memory inputs k = Some observed ->
 generated_legal_trace memory inputs k ->
 VM.find 1 (formal_external_inputs (generated_observation_input inputs k)) = Some (Gval (Fuint 1) [::false]) ->
 dut_node_low_zero 408 (top_environment observed) /\ dut_node_low_zero 418 (top_environment observed).
Proof.
 intros Observe Legal Reset.
 destruct (dut_no_trap_observed_context memory inputs k observed Observe Legal Reset)
 as [history [Last [Boundary [Steps NoTrap]]]].
 destruct (dut_no_trap_invalid_flags_history (generated_observation_input inputs k) nil history 9259 9258 Boundary Steps ltac:(vm_compute;lia) ltac:(vm_compute;lia)
   (NoTrap 9258 ltac:(vm_compute;lia) ltac:(vm_compute;lia))) as [Instruction Load].
 split; intros width bits Lookup; rewrite <- Last in Lookup.
 - rewrite <- (exception_stable_408_history (generated_observation_input inputs k) nil history 9259 Boundary Steps 9258 9259 ltac:(vm_compute;lia) ltac:(vm_compute;lia) ltac:(vm_compute;lia) (le_n 9259)) in Lookup.
   exact (Instruction width bits Lookup).
 - rewrite <- (exception_stable_418_history (generated_observation_input inputs k) nil history 9259 Boundary Steps 9258 9259 ltac:(vm_compute;lia) ltac:(vm_compute;lia) ltac:(vm_compute;lia) (le_n 9259)) in Lookup.
   exact (Load width bits Lookup).
Qed.
Theorem dut_no_trap_target_aligned_observed memory inputs k observed target compressed :
 generated_observe memory inputs k = Some observed ->
 generated_legal_trace memory inputs k ->
 VM.find 1 (formal_external_inputs (generated_observation_input inputs k)) = Some (Gval (Fuint 1) [::false]) ->
 VM.find 7760 (top_environment observed) = Some (Gval (Fuint 1) [::true]) ->
 VM.find 7752 (top_environment observed) = Some (Gval (Fuint 32) target) ->
 size target = 32%nat ->
 reference_redirect_aligned compressed (N.clearbit (to_N target) 0) = true.
Proof.
 intros Observe Legal Reset Redirect Target Size.
 pose proof (dut_no_trap_target_bit_observed memory inputs k observed target Observe Legal Reset Redirect Target Size) as Bit.
 rewrite reference_redirect_aligned_bits N.clearbit_eq N.clearbit_neq; [|discriminate].
 rewrite Bit. destruct compressed; reflexivity.
Qed.
