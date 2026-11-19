Require Import DUTRedirectSemantics FormalLocalHistory ObservedJointRegisterConcrete CoreSocModel ComparisonNodes ReferenceRedirectSpine SelectedNodeSafety X0ConcretePositionCertificate X0ConcreteSafetyCertificate ReferenceLoadSemantics.
From Coq Require Import NArith ZArith List Lia PeanoNat.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From nbits Require Import NBits.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Firrtl_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Definition rf_subtract_ref_expr_3457 := (@Eref VarOrder.T (@Eid VarOrder.T 2209)).
Definition rf_subtract_ref_expr_3458 := (@Eref VarOrder.T (@Eid VarOrder.T 2804)).
Definition rf_subtract_ref_expr_3459 := (@Eprim_binop VarOrder.T Bsub (@Eref VarOrder.T (@Eid VarOrder.T 3457)) (@Eref VarOrder.T (@Eid VarOrder.T 3458))).
Definition rf_subtract_ref_expr_3460 := (@Eprim_unop VarOrder.T (Utail 1) (@Eref VarOrder.T (@Eid VarOrder.T 3459))).
Definition rf_subtract_ref_expr_3461 := (@Eref VarOrder.T (@Eid VarOrder.T 3460)).
Definition rf_subtract_ref_nodes := [::(3457,rf_subtract_ref_expr_3457);(3458,rf_subtract_ref_expr_3458);(3459,rf_subtract_ref_expr_3459);(3460,rf_subtract_ref_expr_3460);(3461,rf_subtract_ref_expr_3461)].
Definition rf_subtract_ref_offsets := [::3536%nat;0%nat;0%nat;0%nat;0%nat].
Lemma rf_subtract_ref_positions :select_node_offsets rf_subtract_ref_offsets flat_statements=Some rf_subtract_ref_nodes.
Proof. vm_compute;reflexivity. Qed.
Lemma rf_subtract_ref_safety :selected_node_safety flat_memories flat_statements rf_subtract_ref_offsets flat_statements=true.
Proof. vm_compute;reflexivity. Qed.
Local Opaque flat_statements flat_memories generated_modules generated_top.

(* Handwritten semantic composition. *)
Theorem rf_reference_subtract_four invalid s0 s1 s2 s3 s4 left right :
 (forall old, old=s0 \/ old=s1 ->VM.find 2209 old=Some(Gval(Fuint 32)left)) ->
 (forall old, old=s0 \/ old=s1 ->VM.find 2804 old=Some(Gval(Fuint 32)right)) ->
 formal_value_iter invalid flat_memories s0 false s0 flat_statements=Some s1 ->
 formal_value_iter invalid flat_memories s1 false s1 flat_statements=Some s2 ->
 formal_value_iter invalid flat_memories s2 false s2 flat_statements=Some s3 ->
 formal_value_iter invalid flat_memories s3 false s3 flat_statements=Some s4 ->
 VM.find 3461 s4=Some(Gval(Fuint 32)(dut_branch_difference left right)).
Proof.
 intros Left Right S1 S2 S3 S4.
 pose proof(Left s0(or_introl(Logic.eq_refl _)))as L.
 pose proof(Right s0(or_introl(Logic.eq_refl _)))as R.

assert(V3457:VM.find 3457 s1=Some(Gval(Fuint 32)left)).
{eapply(reference_redirect_ground_step rf_subtract_ref_offsets rf_subtract_ref_nodes 3457 rf_subtract_ref_expr_3457);[exact rf_subtract_ref_positions|exact rf_subtract_ref_safety|apply(List.nth_error_In rf_subtract_ref_nodes 0%nat);reflexivity| |exact S1].
intros site. cbn[rf_subtract_ref_expr_3457 eval_hfexpr_validif_policy eval_href_validif_policy]. rewrite L. reflexivity.
}
assert(V3458:VM.find 3458 s1=Some(Gval(Fuint 32)right)).
{eapply(reference_redirect_ground_step rf_subtract_ref_offsets rf_subtract_ref_nodes 3458 rf_subtract_ref_expr_3458);[exact rf_subtract_ref_positions|exact rf_subtract_ref_safety|apply(List.nth_error_In rf_subtract_ref_nodes 1%nat);reflexivity| |exact S1].
intros site. cbn[rf_subtract_ref_expr_3458 eval_hfexpr_validif_policy eval_href_validif_policy]. rewrite R. reflexivity.
}
assert(Sum:VM.find 3459 s2=Some(Gval(Fuint 33)(from_Z 33(to_Zpos left-to_Zpos right)%Z))).
{eapply(reference_redirect_ground_step rf_subtract_ref_offsets rf_subtract_ref_nodes 3459 rf_subtract_ref_expr_3459);[exact rf_subtract_ref_positions|exact rf_subtract_ref_safety|apply(List.nth_error_In rf_subtract_ref_nodes 2%nat);reflexivity| |exact S2].
intros site. cbn[rf_subtract_ref_expr_3459 eval_hfexpr_validif_policy eval_href_validif_policy]. rewrite V3457 V3458. reflexivity.
}
assert(Tail:VM.find 3460 s3=Some(Gval(Fuint 32)(dut_branch_difference left right))).
{eapply(reference_redirect_ground_step rf_subtract_ref_offsets rf_subtract_ref_nodes 3460 rf_subtract_ref_expr_3460);[exact rf_subtract_ref_positions|exact rf_subtract_ref_safety|apply(List.nth_error_In rf_subtract_ref_nodes 3%nat);reflexivity| |exact S3].
intros site. cbn[rf_subtract_ref_expr_3460 eval_hfexpr_validif_policy eval_href_validif_policy]. rewrite Sum. reflexivity.
}
eapply(reference_redirect_ground_step rf_subtract_ref_offsets rf_subtract_ref_nodes 3461 rf_subtract_ref_expr_3461);[exact rf_subtract_ref_positions|exact rf_subtract_ref_safety|apply(List.nth_error_In rf_subtract_ref_nodes 4%nat);reflexivity| |exact S4].
intros site. cbn[rf_subtract_ref_expr_3461 eval_hfexpr_validif_policy eval_href_validif_policy]. rewrite Tail. reflexivity.

Qed.
Require Import FormalObservedHistory ReferenceControlStabilityHistory.
Theorem rf_reference_subtract_observed memory inputs k observed left right :
 generated_observe memory inputs k=Some observed ->generated_legal_trace memory inputs k ->
 VM.find 2209 (top_environment observed)=Some(Gval(Fuint 32)left) ->
 VM.find 2804 (top_environment observed)=Some(Gval(Fuint 32)right) ->
 VM.find 3461 (top_environment observed)=Some(Gval(Fuint 32)(dut_branch_difference left right)).
Proof.
 intros Observe Legal Left Right.
 destruct(observed_history memory inputs k observed Observe Legal)as[reset[history[Last[Steps Resets]]]].
 assert(L:forall time,(9255<=time)%coq_nat ->(time<=9259)%coq_nat ->VM.find 2209 (history time)=Some(Gval(Fuint 32)left)).
 { intros time Lower Upper.
 rewrite(reference_control_stable_2209_history(generated_observation_input inputs k)nil history 9259 reset Resets Steps time 9259 ltac:(apply (Nat.le_trans _ 9255 _);[vm_compute;lia|exact Lower])ltac:(vm_compute;lia)Upper ltac:(vm_compute;lia))Last;exact Left. }
 assert(R:forall time,(9255<=time)%coq_nat ->(time<=9259)%coq_nat ->VM.find 2804 (history time)=Some(Gval(Fuint 32)right)).
 { intros time Lower Upper.
 rewrite(reference_control_stable_2804_history(generated_observation_input inputs k)nil history 9259 reset Resets Steps time 9259 ltac:(apply (Nat.le_trans _ 9255 _);[vm_compute;lia|exact Lower])ltac:(vm_compute;lia)Upper ltac:(vm_compute;lia))Last;exact Right. }
 rewrite<-Last.
 apply(rf_reference_subtract_four(formal_invalid_policy(generated_observation_input inputs k)nil)(history 9255%nat)(history 9256%nat)(history 9257%nat)(history 9258%nat)(history 9259%nat)left right).
 - intros old[Same|Same];subst old;apply L;vm_compute;lia.
 - intros old[Same|Same];subst old;apply R;vm_compute;lia.
 - apply Steps;vm_compute;lia.
 - apply Steps;vm_compute;lia.
 - apply Steps;vm_compute;lia.
 - apply Steps;vm_compute;lia.
Qed.
Require Import RFSubtractReferencePorts RFAddReferenceData RFAddCycle RFAddReferencePorts RFALUArithmeticData ReferenceALUIImmediate RFALUReferenceData ReferenceBankCycleInputs RFEffectState RFScalarControl RFReferenceWriteEffect RFReferenceNopHistory RFWriteEffect RFReadPorts ReferenceInstructionDecode ReferenceLoadSemantics FormalLocalHistory CoreSocModel.
Definition cycle_subtract_semantics(bank:rf_bank)instruction :=
 dut_branch_difference(bank(to_nat(rf_instruction_address false instruction)))
 (bank(to_nat(rf_instruction_address true instruction))).
Lemma cycle_subtract_semantics_size bank instruction :size(cycle_subtract_semantics bank instruction)=32%nat.
Proof. unfold cycle_subtract_semantics,dut_branch_difference. rewrite size_take size_from_Z;reflexivity. Qed.
Theorem rf_subtract_reference_data_active memory inputs k observed instruction bank :
 generated_observe memory inputs k=Some observed ->generated_legal_trace memory inputs k ->
 VM.find 1(formal_external_inputs(generated_observation_input inputs k))=Some(Gval(Fuint 1)[::false]) ->
 VM.find 1707(top_environment observed)=Some(Gval(Fuint 1)[::true]) ->
 VM.find 7750(top_environment observed)=Some(Gval(Fuint 32)instruction) ->
 N.land(to_N instruction)(reference_instruction_mask 19%nat)=reference_instruction_code 19%nat ->
 rf_reference_bank_at(top_environment observed)bank ->
 VM.find 3461(top_environment observed)=Some(Gval(Fuint 32)(cycle_subtract_semantics bank instruction)).
Proof.
 intros Observe Legal Reset Enabled Instruction Match Bank.
 unfold cycle_subtract_semantics. apply(rf_reference_subtract_observed memory inputs k observed _ _ Observe Legal).
 - exact(rf_subtract_bank_observed false memory inputs k observed instruction bank Observe Legal Enabled Instruction Match Bank).
 - exact(rf_subtract_bank_observed true memory inputs k observed instruction bank Observe Legal Enabled Instruction Match Bank).

Qed.
Lemma rf_subtract_write_node :rf_reference_write_data(rf_isa_write_stage 19%nat)=3461.
Proof. reflexivity. Qed.
Theorem rf_subtract_reference_word_active memory inputs k observed instruction bank :
 generated_observe memory inputs k=Some observed ->generated_legal_trace memory inputs k ->
 VM.find 1(formal_external_inputs(generated_observation_input inputs k))=Some(Gval(Fuint 1)[::false]) ->
 VM.find 1707(top_environment observed)=Some(Gval(Fuint 1)[::true]) ->
 VM.find 7750(top_environment observed)=Some(Gval(Fuint 32)instruction) ->
 N.land(to_N instruction)(reference_instruction_mask 19%nat)=reference_instruction_code 19%nat ->
 rf_reference_bank_at(top_environment observed)bank ->
 ref_write_word(top_environment observed)(rf_isa_write_stage 19%nat)=cycle_subtract_semantics bank instruction.
Proof.
 intros Observe Legal Reset Enabled Instruction Match Bank.
 pose proof(rf_subtract_reference_data_active memory inputs k observed instruction bank Observe Legal Reset Enabled Instruction Match Bank)as Data.
 unfold ref_write_word. rewrite(rf_subtract_write_node)Data.
 change(take 32(cycle_subtract_semantics bank instruction)=cycle_subtract_semantics bank instruction).
 rewrite<-(cycle_subtract_semantics_size bank instruction). apply take_size.
Qed.
Theorem rf_subtract_reference_effect_active memory inputs k observed instruction bank :
 generated_observe memory inputs k=Some observed ->generated_legal_trace memory inputs k ->
 VM.find 1(formal_external_inputs(generated_observation_input inputs k))=Some(Gval(Fuint 1)[::false]) ->
 VM.find 1707(top_environment observed)=Some(Gval(Fuint 1)[::true]) ->
 VM.find 7750(top_environment observed)=Some(Gval(Fuint 32)instruction) ->
 N.land(to_N instruction)(reference_instruction_mask 19%nat)=reference_instruction_code 19%nat ->
 rf_reference_bank_at(top_environment observed)bank ->
 ref_write_effect(top_environment observed)=RFWrite(to_nat(rf_instruction_rd instruction))(cycle_subtract_semantics bank instruction).
Proof.
 intros Observe Legal Reset Enabled Instruction Match Bank.
 assert(Row:(19<37)%coq_nat)by lia.
 assert(Writes:rf_isa_writes 19%nat =true)by reflexivity.
 destruct(rf_destination_class_observed memory inputs k observed instruction 19%nat Observe Legal Instruction Enabled Row Match)as[DutRd RefRd].
 rewrite Writes in RefRd. unfold ref_write_effect. rewrite(ref_write_bit_actual _ _ _ Enabled).
 unfold ref_write_destination. rewrite RefRd.
 rewrite(rf_reference_effect_guards_ext (ref_write_guard(top_environment observed))(rf_write_opcode_bit instruction)).
 2:{ intros stage Stage. destruct(rf_write_decoder_certificate stage Stage)as[Bound Node].
 unfold ref_write_guard. rewrite Node. rewrite(ref_write_bit_actual _ _ _ (rf_reference_decoder_observed memory inputs k observed instruction(rf_write_decoder_index stage)Observe Legal Instruction Enabled Bound)). reflexivity. }
 rewrite(rf_reference_class_write_effect instruction 19%nat _ _ _ Row Match Writes).
 assert(Permission:rf_reference_permission_value(rf_isa_write_stage 19%nat)(ref_write_permission(top_environment observed)(rf_isa_write_stage 19%nat))=true).
 { reflexivity. }
 rewrite Permission(rf_subtract_reference_word_active memory inputs k observed instruction bank Observe Legal Reset Enabled Instruction Match Bank). reflexivity.
Qed.
