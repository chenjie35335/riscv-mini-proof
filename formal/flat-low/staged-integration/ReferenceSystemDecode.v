Require Import CoreSocModel ComparisonNodes ReferenceRedirectSpine ReferenceControlExpressions ReferenceControlNodeCertificates0 ReferenceControlNodeCongruence0.
From Coq Require Import ZArith Lia.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From nbits Require Import NBits.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Firrtl_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Theorem reference_system_decode_history invalid s0 s1 s2 instruction breakpoint :
 size instruction = 32%nat ->
 VM.find 1884 s0 = Some (Gval (Fuint 32) instruction) ->
 formal_value_iter invalid flat_memories s0 false s0 flat_statements = Some s1 ->
 formal_value_iter invalid flat_memories s1 false s1 flat_statements = Some s2 ->
 VM.find (if breakpoint then 1937 else 1933) s2 = Some (Gval (Fuint 1)
 [::N.eqb (to_N instruction) (if breakpoint then 1048691 else 115)]).
Proof.
 intros Size Instruction S1 S2.
 assert (Mask : VM.find (if breakpoint then 1936 else 1932) s1 = Some (Gval (Fuint 32) instruction)).
 { eapply (reference_redirect_ground_step reference_control_0_offsets reference_control_0_nodes _
 (if breakpoint then reference_control_expr_1936 else reference_control_expr_1932));
 [exact reference_control_0_positions|exact reference_control_0_safety|destruct breakpoint;[exact reference_control_member_1936|exact reference_control_member_1932]| |exact S1].
 intros site. destruct breakpoint;
 cbn [reference_control_expr_1936 reference_control_expr_1932 eval_hfexpr_validif_policy eval_href_validif_policy];rewrite Instruction;
 change (Some (Gval (Fuint 32) (andB instruction (ones 32))) = Some (Gval (Fuint 32) instruction));
 rewrite -Size andB1;reflexivity. }
 eapply (reference_redirect_ground_step reference_control_0_offsets reference_control_0_nodes _
 (if breakpoint then reference_control_expr_1937 else reference_control_expr_1933));
 [exact reference_control_0_positions|exact reference_control_0_safety|destruct breakpoint;[exact reference_control_member_1937|exact reference_control_member_1933]| |exact S2].
 intros site. destruct breakpoint;
 cbn [reference_control_expr_1937 reference_control_expr_1933 eval_hfexpr_validif_policy eval_href_validif_policy] in *;
 rewrite Mask; cbn [size]; rewrite ltnn; cbn [zext_to]; rewrite ?subnn;
 cbn [zext zeros nseq cat]; unfold eval_binop; cbn [eval_binop_basic];
 repeat match goal with |- context [absorbing_bit ?op ?left ?right] => destruct (absorbing_bit op left right) end;
 cbn [refine_boolean_result]; rewrite redirect_N_eqb N.eqb_sym; reflexivity.
Qed.
Require Import MemoryRequestObservedSemantics FormalObservedHistory ObservedJointRegisterConcrete LoadTypeCorrespondence JointUpdateBoundaryHistory ReferenceControlStabilityHistory FormalLocalHistory.
Theorem reference_system_decode_observed memory inputs k observed instruction enabled breakpoint :
 generated_observe memory inputs k = Some observed -> generated_legal_trace memory inputs k ->
 VM.find 7750 (top_environment observed) = Some (Gval (Fuint 32) instruction) ->
 VM.find 1707 (top_environment observed) = Some (Gval (Fuint 1) [::enabled]) ->
 VM.find (if breakpoint then 1937 else 1933) (top_environment observed) =
 Some (Gval (Fuint 1) [::N.eqb (to_N (memory_reference_instruction instruction enabled)) (if breakpoint then 1048691 else 115)]).
Proof.
 intros Observe Legal Instruction Enabled.
 destruct (observed_joint_register_concrete memory inputs k observed 7750%nat 32%nat Observe Legal load_type_instruction_member) as [word [Size Word]].
 rewrite Instruction in Word. inversion Word;subst word.
 destruct (observed_history memory inputs k observed Observe Legal) as [reset [history [Last [Steps Resets]]]].
 assert (Inst : forall t, (t <= 9259)%coq_nat -> VM.find 7750 (history t) = Some (Gval (Fuint 32) instruction)).
 { intros t Upper. pose proof (joint_update_register_history_same _ history 9259 7750 32 load_type_instruction_member Steps) as Hold.
   rewrite (Hold t Upper). rewrite <- (Hold 9259%nat ltac:(lia)). rewrite Last. exact Instruction. }
 assert (Enable : forall t, (200 <= t)%coq_nat -> (t <= 9259)%coq_nat -> VM.find 1707 (history t) = Some (Gval (Fuint 1) [::enabled])).
 { intros t Lower Upper. rewrite (reference_control_stable_1707_history (generated_observation_input inputs k) nil history 9259 reset Resets Steps t 9259%nat ltac:(lia) ltac:(lia) Upper ltac:(lia)) Last. exact Enabled. }
 pose proof (memory_reference_instruction_history _ history 9259 200 instruction enabled Size Steps Inst Enable 9257 ltac:(vm_compute;lia) ltac:(vm_compute;lia)) as Source.
 rewrite <- Last.
 eapply reference_system_decode_history;[|exact Source|apply Steps;vm_compute;lia|apply Steps;vm_compute;lia].
 unfold memory_reference_instruction. destruct enabled;[exact Size|apply size_from_N].
Qed.
Require Import EventAssertionSemantics CSRCommandCorrespondence.
Theorem reference_system_absent_observed memory inputs k observed instruction enabled breakpoint :
 generated_observe memory inputs k = Some observed -> generated_legal_trace memory inputs k ->
 VM.find 1 (formal_external_inputs (generated_observation_input inputs k)) = Some (Gval (Fuint 1) [::false]) ->
 VM.find 7750 (top_environment observed) = Some (Gval (Fuint 32) instruction) ->
 VM.find 1707 (top_environment observed) = Some (Gval (Fuint 1) [::enabled]) ->
 VM.find (if breakpoint then 1937 else 1933) (top_environment observed) = Some (Gval (Fuint 1) [::false]).
Proof.
 intros Observe Legal Reset Instruction Enabled.
 rewrite (reference_system_decode_observed memory inputs k observed instruction enabled breakpoint Observe Legal Instruction Enabled).
 destruct enabled;[|destruct breakpoint;reflexivity].
 cbn [memory_reference_instruction].
 assert (Size : size instruction = 32%nat).
 { destruct (observed_joint_register_concrete memory inputs k observed 7750%nat 32%nat Observe Legal load_type_instruction_member) as [word [Size Word]].
 rewrite Instruction in Word. inversion Word;subst word;exact Size. }
 assert (Different : N.eqb (to_N instruction) (if breakpoint then 1048691 else 115) = false).
 { apply N.eqb_neq. intro Equal.
   pose proof (from_N_to_N instruction) as Roundtrip. rewrite Size Equal in Roundtrip.
   apply (event_no_ecall_ebreak_instruction memory inputs k observed instruction (if breakpoint then 1%nat else 0%nat) Observe Legal Reset).
   - destruct breakpoint;lia.
   - exact Instruction.
   - unfold csr_system_instruction. destruct breakpoint;exact (Logic.eq_sym Roundtrip). }
 rewrite Different;reflexivity.
Qed.
