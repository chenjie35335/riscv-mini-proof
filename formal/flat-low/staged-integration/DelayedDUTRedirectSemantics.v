Require Import DUTRedirectSemantics ReferenceRedirectSemantics ReferenceRedirectSpine
 ObservedInstructionNormalTransfer DelayedRedirectObserved JointBoundaryPreparation
 JointBoundaryRegisters StagedObservedRegister StagedCircuitRegisterHold FormalFetchType
 ReferenceControlWires0 ReferenceControlWires3 ReferenceControlStabilityHistory
 ReferenceControlNodeCertificates0 ReferenceControlNodeCongruence0 ReferenceControlExpressions
 FormalDeclaredConnection FormalObservedHistory FormalLocalHistory CoreSocModel ComparisonNodes.
From Coq Require Import NArith ZArith Lia List.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From nbits Require Import NBitsDef NBitsOp.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths
 HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Local Opaque flat_statements flat_memories generated_modules generated_top.
(* The front instruction and raw redirect belong to cycle k; the writeback
   instruction, delayed redirect, and enabled reference decode align at k+1. *)
Lemma delayed_joint_observed_copy memory inputs k committed observed node width :
 List.In (node,width) joint_boundary_registers ->
 generated_run memory inputs k = Some committed ->
 generated_observe memory inputs k = Some observed ->
 VM.find (N.of_nat node) (top_environment observed) =
 VM.find (N.of_nat node) (top_environment committed).
Proof.
 intros Member Run Observe.
 destruct (fetch9220_run_type memory inputs k committed Run) as [old [value [Old Rest]]].
 pose proof joint_boundary_preparation_check as Check.
 rewrite List.forallb_forall in Check. specialize (Check (node,width) Member).
 cbn [fst snd] in Check. move/andP: Check => [/andP [Safe NotClock] NotReset].
 destruct (joint_boundary_register_properties node width Member) as [_ Present].
 pose proof (staged_observed_register_copies memory inputs k committed old observed (N.of_nat node)
 NotClock NotReset Safe Present Run Old Observe) as Copy.
 unfold staged_register_lookup in Copy. unfold top_environment. rewrite Old.
 destruct (SVM.find nil observed); exact Copy.
Qed.
Theorem delayed_instruction_redirect_pair memory inputs k observed committed next_observed front bit :
 generated_observe memory inputs k = Some observed ->
 generated_legal_trace memory inputs k ->
 generated_run memory inputs (S k) = Some committed ->
 generated_observe memory inputs (S k) = Some next_observed ->
 VM.find 1 (formal_external_inputs (generated_observation_input inputs k)) = Some (Gval (Fuint 1) [::false]) ->
 size front = 32%nat ->
 VM.find 7748 (top_environment observed) = Some (Gval (Fuint 32) front) ->
 VM.find 7773 (top_environment observed) = Some (Gval (Fuint 1) [::bit]) ->
 VM.find 7750 (top_environment next_observed) = Some (Gval (Fuint 32) front) /\
 VM.find 7760 (top_environment next_observed) = Some (Gval (Fuint 1) [::bit]).
Proof.
 intros Observe Legal Run NextObserve Reset Size Front Redirect.
 split.
 - rewrite (delayed_joint_observed_copy memory inputs (S k) committed next_observed 7750 32
    ltac:(apply (List.nth_error_In joint_boundary_registers 55%nat); vm_compute; reflexivity) Run NextObserve).
   exact (observed_instruction_normal_transfer memory inputs k observed committed front Observe Legal Run Reset Size Front).
 - rewrite (delayed_joint_observed_copy memory inputs (S k) committed next_observed 7760 1
    ltac:(apply (List.nth_error_In joint_boundary_registers 65%nat); vm_compute; reflexivity) Run NextObserve).
   exact (delayed_redirect_observed_step memory inputs k observed committed bit Observe Legal Run Reset Redirect).
Qed.

(* The operand test relation compares cycle k DUT operands with cycle k+1
   reference operands. Enabled instruction propagation and decode matching
   remain explicit obligations; no same-cycle redirect equality is assumed. *)
Theorem delayed_dut_reference_redirect_observed memory inputs k observed committed next_observed
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
 VM.find 1884 (top_environment next_observed) = Some (Gval (Fuint 32) instruction) ->
 VM.find 2209 (top_environment next_observed) = Some (Gval (Fuint 32) ref_left) ->
 VM.find 2804 (top_environment next_observed) = Some (Gval (Fuint 32) ref_right) ->
 VM.find 2552 (top_environment next_observed) = Some (Gval (Fuint 32) immediate) ->
 VM.find 7331 (top_environment next_observed) = Some (Gval (Fuint 32) pc) ->
 VM.find 7332 (top_environment next_observed) = Some (Gval (Fuint 32) csr) ->
 size dut_left = 32%nat -> size dut_right = 32%nat ->
 size ref_left = 32%nat -> size ref_right = 32%nat -> size pc = 32%nat -> size csr = 32%nat ->
 dut_redirect_controls_match (to_N instruction) (to_N selector) (to_N kind) ->
 dut_operand_tests_match (to_N kind) (to_N dut_left) (to_N dut_right) (to_N ref_left) (to_N ref_right) ->
 (dut_reference_taken (to_N instruction) (to_N ref_left) (to_N ref_right) = true ->
  reference_redirect_aligned (N.testbit (to_N csr) 2) (to_N pc + to_N immediate) = true) ->
 (N.eqb (N.land (to_N instruction) 28799) 103 = true ->
  reference_redirect_aligned (N.testbit (to_N csr) 2) (N.clearbit (to_N ref_left + to_N immediate) 0) = true) ->
 VM.find 7760 (top_environment next_observed) = VM.find 6507 (top_environment next_observed).
Proof.
 intros Observe Run NextObserve NextLegal Reset Legal DutLeft DutRight Kind Selector Instruction RefLeft RefRight Immediate Pc Csr
 DutLeftSize DutRightSize RefLeftSize RefRightSize PcSize CsrSize Controls Operands BranchAligned JalrAligned.
 pose proof (dut_redirect_observed memory inputs k observed dut_left dut_right kind selector Observe Legal DutLeft DutRight Kind Selector DutLeftSize DutRightSize) as Raw.
 rewrite (delayed_joint_observed_copy memory inputs (S k) committed next_observed 7760 1
    ltac:(apply (List.nth_error_In joint_boundary_registers 65%nat); vm_compute; reflexivity) Run NextObserve).
 rewrite (delayed_redirect_observed_step memory inputs k observed committed _ Observe Legal Run Reset Raw).
 rewrite (reference_redirect_function_observed memory inputs (S k) next_observed instruction ref_left ref_right immediate pc csr NextObserve NextLegal Instruction RefLeft RefRight Immediate Pc Csr RefLeftSize RefRightSize PcSize CsrSize).
 rewrite (dut_redirect_reference (to_N instruction) (to_N selector) (to_N kind) (to_N dut_left) (to_N dut_right) (to_N ref_left) (to_N ref_right) (to_N immediate) (to_N pc) (to_N csr) Controls Operands BranchAligned JalrAligned).
 reflexivity.
Qed.

Theorem delayed_reference_instruction_history inputs path history limit reset time instruction :
 (forall i, (i <= limit)%coq_nat -> VM.find 1 (history i) = Some (Gval (Fuint 1) [::reset])) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 (127 <= time)%coq_nat -> (time < limit)%coq_nat ->
 VM.find 7750 (history time) = Some (Gval (Fuint 32) instruction) ->
 VM.find 1395 (history time) = Some (Gval (Fuint 1) [::true]) ->
 size instruction = 32%nat ->
 VM.find 1884 (history time) = Some (Gval (Fuint 32) instruction).
Proof.
 intros Resets Steps Lower Upper H7750 H1395 Size.
 pose proof (Steps time Upper) as Step.
 assert (H1396 : VM.find 1396 (history time) = Some (Gval (Fuint 32) instruction)).
 { rewrite (reference_control_stable_1396_history inputs path history limit reset Resets Steps time (S time) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)).
 eapply (declared_connection_value 1475 flat_statements reference_control_wire_1396_decl reference_control_wire_1396_mid reference_control_wire_1396_tail 1396 7750 32 (Gval (Fuint 32) instruction));
 [exact reference_control_wire_1396_position|exact reference_control_wire_1396_split|exact reference_control_wire_1396_straight|exact reference_control_wire_1396_mid_safe|exact reference_control_wire_1396_tail_safe|exact reference_control_wire_1396_nonregister|reflexivity|exact H7750|apply reference_redirect_adapt_word; exact Size|exact Step]. }
 assert (H1516 : VM.find 1516 (history time) = Some (Gval (Fuint 32) instruction)).
 { rewrite (reference_control_stable_1516_history inputs path history limit reset Resets Steps time (S time) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)).
 eapply (declared_connection_value 1595 flat_statements reference_control_wire_1516_decl reference_control_wire_1516_mid reference_control_wire_1516_tail 1516 1396 32 (Gval (Fuint 32) instruction));
 [exact reference_control_wire_1516_position|exact reference_control_wire_1516_split|exact reference_control_wire_1516_straight|exact reference_control_wire_1516_mid_safe|exact reference_control_wire_1516_tail_safe|exact reference_control_wire_1516_nonregister|reflexivity|exact H1396|apply reference_redirect_adapt_word; exact Size|exact Step]. }
 assert (H1706 : VM.find 1706 (history time) = Some (Gval (Fuint 32) instruction)).
 { rewrite (reference_control_stable_1706_history inputs path history limit reset Resets Steps time (S time) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)).
 eapply (declared_connection_value 1785 flat_statements reference_control_wire_1706_decl reference_control_wire_1706_mid reference_control_wire_1706_tail 1706 1516 32 (Gval (Fuint 32) instruction));
 [exact reference_control_wire_1706_position|exact reference_control_wire_1706_split|exact reference_control_wire_1706_straight|exact reference_control_wire_1706_mid_safe|exact reference_control_wire_1706_tail_safe|exact reference_control_wire_1706_nonregister|reflexivity|exact H1516|apply reference_redirect_adapt_word; exact Size|exact Step]. }
 assert (H1517 : VM.find 1517 (history time) = Some (Gval (Fuint 1) [::true])).
 { rewrite (reference_control_stable_1517_history inputs path history limit reset Resets Steps time (S time) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)).
 eapply (declared_connection_value 1596 flat_statements reference_control_wire_1517_decl reference_control_wire_1517_mid reference_control_wire_1517_tail 1517 1395 1 (Gval (Fuint 1) [::true]));
 [exact reference_control_wire_1517_position|exact reference_control_wire_1517_split|exact reference_control_wire_1517_straight|exact reference_control_wire_1517_mid_safe|exact reference_control_wire_1517_tail_safe|exact reference_control_wire_1517_nonregister|reflexivity|exact H1395|reflexivity|exact Step]. }
 assert (H1707 : VM.find 1707 (history time) = Some (Gval (Fuint 1) [::true])).
 { rewrite (reference_control_stable_1707_history inputs path history limit reset Resets Steps time (S time) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)).
 eapply (declared_connection_value 1786 flat_statements reference_control_wire_1707_decl reference_control_wire_1707_mid reference_control_wire_1707_tail 1707 1517 1 (Gval (Fuint 1) [::true]));
 [exact reference_control_wire_1707_position|exact reference_control_wire_1707_split|exact reference_control_wire_1707_straight|exact reference_control_wire_1707_mid_safe|exact reference_control_wire_1707_tail_safe|exact reference_control_wire_1707_nonregister|reflexivity|exact H1517|reflexivity|exact Step]. }
 assert (H1883 : VM.find 1883 (history time) = Some (Gval (Fuint 32) instruction)).
 { rewrite (reference_control_stable_1883_history inputs path history limit reset Resets Steps time (S time) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)).
 eapply (reference_redirect_ground_step reference_control_0_offsets reference_control_0_nodes 1883 reference_control_expr_1883);
 [exact reference_control_0_positions|exact reference_control_0_safety|exact reference_control_member_1883| |exact Step].
 intros site. unfold reference_control_expr_1883. cbn [eval_hfexpr_validif_policy eval_href_validif_policy].
 rewrite H1707. cbn. rewrite H1706. cbn. apply reference_redirect_adapt_word; exact Size. }
 assert (H1884 : VM.find 1884 (history time) = Some (Gval (Fuint 32) instruction)).
 { rewrite (reference_control_stable_1884_history inputs path history limit reset Resets Steps time (S time) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)).
 eapply (reference_redirect_ground_step reference_control_0_offsets reference_control_0_nodes 1884 reference_control_expr_1884);
 [exact reference_control_0_positions|exact reference_control_0_safety|exact reference_control_member_1884| |exact Step].
 intros site. unfold reference_control_expr_1884. cbn [eval_hfexpr_validif_policy eval_href_validif_policy].
 exact H1883. }
 exact H1884.
Qed.
Theorem delayed_reference_instruction_observed memory inputs k observed instruction :
 generated_observe memory inputs k = Some observed ->
 generated_legal_trace memory inputs k ->
 VM.find 7750 (top_environment observed) = Some (Gval (Fuint 32) instruction) ->
 VM.find 1395 (top_environment observed) = Some (Gval (Fuint 1) [::true]) ->
 size instruction = 32%nat ->
 VM.find 1884 (top_environment observed) = Some (Gval (Fuint 32) instruction).
Proof.
 intros Observe Legal Instruction Enabled Size.
 destruct (observed_history memory inputs k observed Observe Legal) as [reset [history [Last [Steps Resets]]]].
 rewrite <- Last.
 rewrite <- (reference_control_stable_1884_history (generated_observation_input inputs k) nil history 9259 reset Resets Steps 9258 9259 ltac:(vm_compute;lia) ltac:(vm_compute;lia) ltac:(vm_compute;lia) ltac:(vm_compute;lia)).
 eapply (delayed_reference_instruction_history (generated_observation_input inputs k) nil history 9259 reset 9258 instruction Resets Steps ltac:(vm_compute;lia) ltac:(vm_compute;lia)); try assumption.
 - rewrite (reference_control_stable_7750_history (generated_observation_input inputs k) nil history 9259 reset Resets Steps 9258 9259 ltac:(vm_compute;lia) ltac:(vm_compute;lia) ltac:(vm_compute;lia) ltac:(vm_compute;lia)) Last. exact Instruction.
 - rewrite (reference_control_stable_1395_history (generated_observation_input inputs k) nil history 9259 reset Resets Steps 9258 9259 ltac:(vm_compute;lia) ltac:(vm_compute;lia) ltac:(vm_compute;lia) ltac:(vm_compute;lia)) Last. exact Enabled.
Qed.

(* Full temporal composition. The decoded reference instruction is derived
   from the previous front instruction, guarded by the next checker enable. *)
Theorem delayed_enabled_reference_redirect_observed memory inputs k observed committed next_observed
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
 VM.find 1395 (top_environment next_observed) = Some (Gval (Fuint 1) [::true]) ->
 size instruction = 32%nat ->
 VM.find 2209 (top_environment next_observed) = Some (Gval (Fuint 32) ref_left) ->
 VM.find 2804 (top_environment next_observed) = Some (Gval (Fuint 32) ref_right) ->
 VM.find 2552 (top_environment next_observed) = Some (Gval (Fuint 32) immediate) ->
 VM.find 7331 (top_environment next_observed) = Some (Gval (Fuint 32) pc) ->
 VM.find 7332 (top_environment next_observed) = Some (Gval (Fuint 32) csr) ->
 size dut_left = 32%nat -> size dut_right = 32%nat ->
 size ref_left = 32%nat -> size ref_right = 32%nat -> size pc = 32%nat -> size csr = 32%nat ->
 dut_redirect_controls_match (to_N instruction) (to_N selector) (to_N kind) ->
 dut_operand_tests_match (to_N kind) (to_N dut_left) (to_N dut_right) (to_N ref_left) (to_N ref_right) ->
 (dut_reference_taken (to_N instruction) (to_N ref_left) (to_N ref_right) = true ->
  reference_redirect_aligned (N.testbit (to_N csr) 2) (to_N pc + to_N immediate) = true) ->
 (N.eqb (N.land (to_N instruction) 28799) 103 = true ->
  reference_redirect_aligned (N.testbit (to_N csr) 2) (N.clearbit (to_N ref_left + to_N immediate) 0) = true) ->
 VM.find 7760 (top_environment next_observed) = VM.find 6507 (top_environment next_observed).
Proof.
 intros Observe Run NextObserve NextLegal Reset Legal DutLeft DutRight Kind Selector Front Enabled InstructionSize RefLeft RefRight Immediate Pc Csr
 DutLeftSize DutRightSize RefLeftSize RefRightSize PcSize CsrSize Controls Operands BranchAligned JalrAligned.
 assert (CommittedInstruction : VM.find 7750 (top_environment next_observed) = Some (Gval (Fuint 32) instruction)).
 { rewrite (delayed_joint_observed_copy memory inputs (S k) committed next_observed 7750 32
    ltac:(apply (List.nth_error_In joint_boundary_registers 55%nat); vm_compute; reflexivity) Run NextObserve).
   exact (observed_instruction_normal_transfer memory inputs k observed committed instruction Observe Legal Run Reset InstructionSize Front). }
 pose proof (delayed_reference_instruction_observed memory inputs (S k) next_observed instruction NextObserve NextLegal CommittedInstruction Enabled InstructionSize) as Instruction.
 exact (delayed_dut_reference_redirect_observed memory inputs k observed committed next_observed instruction dut_left dut_right kind selector ref_left ref_right immediate pc csr Observe Run NextObserve NextLegal Reset Legal DutLeft DutRight Kind Selector Instruction RefLeft RefRight Immediate Pc Csr DutLeftSize DutRightSize RefLeftSize RefRightSize PcSize CsrSize Controls Operands BranchAligned JalrAligned).
Qed.
