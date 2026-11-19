Require Import RFCompareArithmetic RFCompareCycle DUTRedirectSemantics FormalLocalHistory ObservedJointRegisterConcrete CoreSocModel ComparisonNodes ReferenceRedirectSpine SelectedNodeSafety X0ConcretePositionCertificate X0ConcreteSafetyCertificate ReferenceLoadSemantics.
From Coq Require Import NArith ZArith List Lia PeanoNat.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From nbits Require Import NBits.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Firrtl_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Definition rf_compare_ref_expr_3484 := (@Eref VarOrder.T (@Eid VarOrder.T 2209)).
Definition rf_compare_ref_expr_3485 := (@Eref VarOrder.T (@Eid VarOrder.T 2804)).
Definition rf_compare_ref_expr_3486 := (@Eprim_binop VarOrder.T (Bcomp Blt) (@Eref VarOrder.T (@Eid VarOrder.T 3484)) (@Eref VarOrder.T (@Eid VarOrder.T 3485))).
Definition rf_compare_ref_expr_3487 := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 3486)) (@Econst VarOrder.T (Fuint 1) [::true]) (@Econst VarOrder.T (Fuint 1) [::false])).
Definition rf_compare_ref_expr_3488 := (@Eprim_unop VarOrder.T (Upad 32) (@Eref VarOrder.T (@Eid VarOrder.T 3487))).
Definition rf_compare_ref_expr_3489 := (@Eref VarOrder.T (@Eid VarOrder.T 2209)).
Definition rf_compare_ref_expr_3490 := (@Ecast VarOrder.T AsSInt (@Eref VarOrder.T (@Eid VarOrder.T 3489))).
Definition rf_compare_ref_expr_3491 := (@Eref VarOrder.T (@Eid VarOrder.T 2804)).
Definition rf_compare_ref_expr_3492 := (@Ecast VarOrder.T AsSInt (@Eref VarOrder.T (@Eid VarOrder.T 3491))).
Definition rf_compare_ref_expr_3493 := (@Eprim_binop VarOrder.T (Bcomp Blt) (@Eref VarOrder.T (@Eid VarOrder.T 3490)) (@Eref VarOrder.T (@Eid VarOrder.T 3492))).
Definition rf_compare_ref_expr_3494 := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 3493)) (@Econst VarOrder.T (Fuint 1) [::true]) (@Econst VarOrder.T (Fuint 1) [::false])).
Definition rf_compare_ref_expr_3495 := (@Eprim_unop VarOrder.T (Upad 32) (@Eref VarOrder.T (@Eid VarOrder.T 3494))).
Definition rf_compare_ref_nodes := [::(3484,rf_compare_ref_expr_3484);(3485,rf_compare_ref_expr_3485);(3486,rf_compare_ref_expr_3486);(3487,rf_compare_ref_expr_3487);(3488,rf_compare_ref_expr_3488);(3489,rf_compare_ref_expr_3489);(3490,rf_compare_ref_expr_3490);(3491,rf_compare_ref_expr_3491);(3492,rf_compare_ref_expr_3492);(3493,rf_compare_ref_expr_3493);(3494,rf_compare_ref_expr_3494);(3495,rf_compare_ref_expr_3495)].
Definition rf_compare_ref_offsets := [::3563%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat].
Lemma rf_compare_ref_positions :select_node_offsets rf_compare_ref_offsets flat_statements=Some rf_compare_ref_nodes.
Proof. vm_compute;reflexivity. Qed.
Lemma rf_compare_ref_safety :selected_node_safety flat_memories flat_statements rf_compare_ref_offsets flat_statements=true.
Proof. vm_compute;reflexivity. Qed.
Local Opaque flat_statements flat_memories generated_modules generated_top.

(* Handwritten semantic composition. *)
Definition rf_compare_reference_output unsigned :=if unsigned then 3488 else 3495.
Theorem rf_reference_compare_five unsigned invalid s0 s1 s2 s3 s4 s5 left right :
 (forall old,old=s0 \/old=s1 ->VM.find 2209 old=Some(Gval(Fuint 32)left)) ->
 (forall old,old=s0 \/old=s1 ->VM.find 2804 old=Some(Gval(Fuint 32)right)) ->
 formal_value_iter invalid flat_memories s0 false s0 flat_statements=Some s1 ->
 formal_value_iter invalid flat_memories s1 false s1 flat_statements=Some s2 ->
 formal_value_iter invalid flat_memories s2 false s2 flat_statements=Some s3 ->
 formal_value_iter invalid flat_memories s3 false s3 flat_statements=Some s4 ->
 formal_value_iter invalid flat_memories s4 false s4 flat_statements=Some s5 ->
 VM.find(rf_compare_reference_output unsigned)s5=Some(Gval(Fuint 32)(rf_compare_word unsigned left right)).
Proof.
 intros Left Right S1 S2 S3 S4 S5. destruct unsigned.
- pose proof(Left s1(or_intror(Logic.eq_refl _)))as L.
 pose proof(Right s1(or_intror(Logic.eq_refl _)))as R.
assert(V3484:VM.find 3484 s2=Some(Gval(Fuint 32)left)).
{eapply(reference_redirect_ground_step rf_compare_ref_offsets rf_compare_ref_nodes 3484 rf_compare_ref_expr_3484);[exact rf_compare_ref_positions|exact rf_compare_ref_safety|apply(List.nth_error_In rf_compare_ref_nodes 0%nat);reflexivity| |exact S2].
intro site. cbn[rf_compare_ref_expr_3484 eval_hfexpr_validif_policy eval_href_validif_policy]. rewrite L;reflexivity. }
assert(V3485:VM.find 3485 s2=Some(Gval(Fuint 32)right)).
{eapply(reference_redirect_ground_step rf_compare_ref_offsets rf_compare_ref_nodes 3485 rf_compare_ref_expr_3485);[exact rf_compare_ref_positions|exact rf_compare_ref_safety|apply(List.nth_error_In rf_compare_ref_nodes 1%nat);reflexivity| |exact S2].
intro site. cbn[rf_compare_ref_expr_3485 eval_hfexpr_validif_policy eval_href_validif_policy]. rewrite R;reflexivity. }
assert(Cmp:VM.find 3486 s3=Some(Gval(Fuint 1)[::rf_compare_bit true left right])).
{eapply(reference_redirect_ground_step rf_compare_ref_offsets rf_compare_ref_nodes 3486 rf_compare_ref_expr_3486);[exact rf_compare_ref_positions|exact rf_compare_ref_safety|apply(List.nth_error_In rf_compare_ref_nodes 2%nat);reflexivity| |exact S3].
intro site. cbn[rf_compare_ref_expr_3486 eval_hfexpr_validif_policy eval_href_validif_policy]. rewrite V3484 V3485;reflexivity. }
assert(Mux:VM.find 3487 s4=Some(Gval(Fuint 1)[::rf_compare_bit true left right])).
{eapply(reference_redirect_ground_step rf_compare_ref_offsets rf_compare_ref_nodes 3487 rf_compare_ref_expr_3487);[exact rf_compare_ref_positions|exact rf_compare_ref_safety|apply(List.nth_error_In rf_compare_ref_nodes 3%nat);reflexivity| |exact S4].
intro site. cbn[rf_compare_ref_expr_3487 eval_hfexpr_validif_policy eval_href_validif_policy]. rewrite Cmp;destruct(rf_compare_bit true left right);reflexivity. }
eapply(reference_redirect_ground_step rf_compare_ref_offsets rf_compare_ref_nodes 3488 rf_compare_ref_expr_3488);[exact rf_compare_ref_positions|exact rf_compare_ref_safety|apply(List.nth_error_In rf_compare_ref_nodes 4%nat);reflexivity| |exact S5].
intro site. cbn[rf_compare_ref_expr_3488 eval_hfexpr_validif_policy eval_href_validif_policy]. rewrite Mux;reflexivity.
- pose proof(Left s0(or_introl(Logic.eq_refl _)))as L.
 pose proof(Right s0(or_introl(Logic.eq_refl _)))as R.
assert(V3489:VM.find 3489 s1=Some(Gval(Fuint 32)left)).
{eapply(reference_redirect_ground_step rf_compare_ref_offsets rf_compare_ref_nodes 3489 rf_compare_ref_expr_3489);[exact rf_compare_ref_positions|exact rf_compare_ref_safety|apply(List.nth_error_In rf_compare_ref_nodes 5%nat);reflexivity| |exact S1].
intro site. cbn[rf_compare_ref_expr_3489 eval_hfexpr_validif_policy eval_href_validif_policy]. rewrite L;reflexivity. }
assert(V3491:VM.find 3491 s1=Some(Gval(Fuint 32)right)).
{eapply(reference_redirect_ground_step rf_compare_ref_offsets rf_compare_ref_nodes 3491 rf_compare_ref_expr_3491);[exact rf_compare_ref_positions|exact rf_compare_ref_safety|apply(List.nth_error_In rf_compare_ref_nodes 7%nat);reflexivity| |exact S1].
intro site. cbn[rf_compare_ref_expr_3491 eval_hfexpr_validif_policy eval_href_validif_policy]. rewrite R;reflexivity. }
assert(V3490:VM.find 3490 s2=Some(Gval(Fsint 32)left)).
{eapply(reference_redirect_ground_step rf_compare_ref_offsets rf_compare_ref_nodes 3490 rf_compare_ref_expr_3490);[exact rf_compare_ref_positions|exact rf_compare_ref_safety|apply(List.nth_error_In rf_compare_ref_nodes 6%nat);reflexivity| |exact S2].
intro site. cbn[rf_compare_ref_expr_3490 eval_hfexpr_validif_policy eval_href_validif_policy]. rewrite V3489;reflexivity. }
assert(V3492:VM.find 3492 s2=Some(Gval(Fsint 32)right)).
{eapply(reference_redirect_ground_step rf_compare_ref_offsets rf_compare_ref_nodes 3492 rf_compare_ref_expr_3492);[exact rf_compare_ref_positions|exact rf_compare_ref_safety|apply(List.nth_error_In rf_compare_ref_nodes 8%nat);reflexivity| |exact S2].
intro site. cbn[rf_compare_ref_expr_3492 eval_hfexpr_validif_policy eval_href_validif_policy]. rewrite V3491;reflexivity. }
assert(Cmp:VM.find 3493 s3=Some(Gval(Fuint 1)[::rf_compare_bit false left right])).
{eapply(reference_redirect_ground_step rf_compare_ref_offsets rf_compare_ref_nodes 3493 rf_compare_ref_expr_3493);[exact rf_compare_ref_positions|exact rf_compare_ref_safety|apply(List.nth_error_In rf_compare_ref_nodes 9%nat);reflexivity| |exact S3].
intro site. cbn[rf_compare_ref_expr_3493 eval_hfexpr_validif_policy eval_href_validif_policy]. rewrite V3490 V3492;reflexivity. }
assert(Mux:VM.find 3494 s4=Some(Gval(Fuint 1)[::rf_compare_bit false left right])).
{eapply(reference_redirect_ground_step rf_compare_ref_offsets rf_compare_ref_nodes 3494 rf_compare_ref_expr_3494);[exact rf_compare_ref_positions|exact rf_compare_ref_safety|apply(List.nth_error_In rf_compare_ref_nodes 10%nat);reflexivity| |exact S4].
intro site. cbn[rf_compare_ref_expr_3494 eval_hfexpr_validif_policy eval_href_validif_policy]. rewrite Cmp;destruct(rf_compare_bit false left right);reflexivity. }
eapply(reference_redirect_ground_step rf_compare_ref_offsets rf_compare_ref_nodes 3495 rf_compare_ref_expr_3495);[exact rf_compare_ref_positions|exact rf_compare_ref_safety|apply(List.nth_error_In rf_compare_ref_nodes 11%nat);reflexivity| |exact S5].
intro site. cbn[rf_compare_ref_expr_3495 eval_hfexpr_validif_policy eval_href_validif_policy]. rewrite Mux;reflexivity.
Qed.
Require Import FormalObservedHistory ReferenceControlStabilityHistory.
Theorem rf_reference_compare_observed memory inputs k observed unsigned left right :
 generated_observe memory inputs k=Some observed ->generated_legal_trace memory inputs k ->
 VM.find 2209 (top_environment observed)=Some(Gval(Fuint 32)left) ->
 VM.find 2804 (top_environment observed)=Some(Gval(Fuint 32)right) ->
 VM.find(rf_compare_reference_output unsigned)(top_environment observed)=Some(Gval(Fuint 32)(rf_compare_word unsigned left right)).
Proof.
 intros Observe Legal Left Right.
 destruct(observed_history memory inputs k observed Observe Legal)as[reset[history[Last[Steps Resets]]]].
 assert(L:forall time,(9254<=time)%coq_nat ->(time<=9259)%coq_nat ->VM.find 2209 (history time)=Some(Gval(Fuint 32)left)).
 { intros time Lower Upper.
 rewrite(reference_control_stable_2209_history(generated_observation_input inputs k)nil history 9259 reset Resets Steps time 9259 ltac:(apply (Nat.le_trans _ 9254 _);[vm_compute;lia|exact Lower])ltac:(vm_compute;lia)Upper ltac:(vm_compute;lia))Last;exact Left. }
 assert(R:forall time,(9254<=time)%coq_nat ->(time<=9259)%coq_nat ->VM.find 2804 (history time)=Some(Gval(Fuint 32)right)).
 { intros time Lower Upper.
 rewrite(reference_control_stable_2804_history(generated_observation_input inputs k)nil history 9259 reset Resets Steps time 9259 ltac:(apply (Nat.le_trans _ 9254 _);[vm_compute;lia|exact Lower])ltac:(vm_compute;lia)Upper ltac:(vm_compute;lia))Last;exact Right. }
 rewrite<-Last.
 apply(rf_reference_compare_five unsigned(formal_invalid_policy(generated_observation_input inputs k)nil)(history 9254%nat)(history 9255%nat)(history 9256%nat)(history 9257%nat)(history 9258%nat)(history 9259%nat)left right).
 - intros old[Same|Same];subst old;apply L;vm_compute;lia.
 - intros old[Same|Same];subst old;apply R;vm_compute;lia.
 - apply Steps;vm_compute;lia.
 - apply Steps;vm_compute;lia.
 - apply Steps;vm_compute;lia.
 - apply Steps;vm_compute;lia.
 - apply Steps;vm_compute;lia.
Qed.
Require Import RFCompareReferencePorts RFAddReferenceData RFAddCycle RFAddReferencePorts RFALUArithmeticData ReferenceALUIImmediate RFALUReferenceData ReferenceBankCycleInputs RFEffectState RFScalarControl RFReferenceWriteEffect RFReferenceNopHistory RFWriteEffect RFReadPorts ReferenceInstructionDecode ReferenceLoadSemantics FormalLocalHistory CoreSocModel.
Definition cycle_compare_semantics unsigned(bank:rf_bank)instruction :=
 rf_compare_word unsigned(bank(to_nat(rf_instruction_address false instruction)))
 (bank(to_nat(rf_instruction_address true instruction))).
Lemma cycle_compare_semantics_size unsigned bank instruction :size(cycle_compare_semantics unsigned bank instruction)=32%nat.
Proof. unfold cycle_compare_semantics. apply rf_compare_word_size. Qed.
Theorem rf_compare_reference_data_active memory inputs k observed instruction unsigned bank :
 generated_observe memory inputs k=Some observed ->generated_legal_trace memory inputs k ->
 VM.find 1(formal_external_inputs(generated_observation_input inputs k))=Some(Gval(Fuint 1)[::false]) ->
 VM.find 1707(top_environment observed)=Some(Gval(Fuint 1)[::true]) ->
 VM.find 7750(top_environment observed)=Some(Gval(Fuint 32)instruction) ->
 N.land(to_N instruction)(reference_instruction_mask (rf_compare_class unsigned))=reference_instruction_code (rf_compare_class unsigned) ->
 rf_reference_bank_at(top_environment observed)bank ->
 VM.find(rf_compare_reference_output unsigned)(top_environment observed)=Some(Gval(Fuint 32)(cycle_compare_semantics unsigned bank instruction)).
Proof.
 intros Observe Legal Reset Enabled Instruction Match Bank.
 unfold cycle_compare_semantics. apply(rf_reference_compare_observed memory inputs k observed unsigned _ _ Observe Legal).
 - exact(rf_compare_bank_observed false memory inputs k observed instruction unsigned bank Observe Legal Enabled Instruction Match Bank).
 - exact(rf_compare_bank_observed true memory inputs k observed instruction unsigned bank Observe Legal Enabled Instruction Match Bank).

Qed.
Lemma rf_compare_write_node unsigned :rf_reference_write_data(rf_isa_write_stage (rf_compare_class unsigned))=rf_compare_reference_output unsigned.
Proof. destruct unsigned;reflexivity. Qed.
Theorem rf_compare_reference_word_active memory inputs k observed instruction unsigned bank :
 generated_observe memory inputs k=Some observed ->generated_legal_trace memory inputs k ->
 VM.find 1(formal_external_inputs(generated_observation_input inputs k))=Some(Gval(Fuint 1)[::false]) ->
 VM.find 1707(top_environment observed)=Some(Gval(Fuint 1)[::true]) ->
 VM.find 7750(top_environment observed)=Some(Gval(Fuint 32)instruction) ->
 N.land(to_N instruction)(reference_instruction_mask (rf_compare_class unsigned))=reference_instruction_code (rf_compare_class unsigned) ->
 rf_reference_bank_at(top_environment observed)bank ->
 ref_write_word(top_environment observed)(rf_isa_write_stage (rf_compare_class unsigned))=cycle_compare_semantics unsigned bank instruction.
Proof.
 intros Observe Legal Reset Enabled Instruction Match Bank.
 pose proof(rf_compare_reference_data_active memory inputs k observed instruction unsigned bank Observe Legal Reset Enabled Instruction Match Bank)as Data.
 unfold ref_write_word. rewrite(rf_compare_write_node unsigned)Data.
 change(take 32(cycle_compare_semantics unsigned bank instruction)=cycle_compare_semantics unsigned bank instruction).
 rewrite<-(cycle_compare_semantics_size unsigned bank instruction). apply take_size.
Qed.
Theorem rf_compare_reference_effect_active memory inputs k observed instruction unsigned bank :
 generated_observe memory inputs k=Some observed ->generated_legal_trace memory inputs k ->
 VM.find 1(formal_external_inputs(generated_observation_input inputs k))=Some(Gval(Fuint 1)[::false]) ->
 VM.find 1707(top_environment observed)=Some(Gval(Fuint 1)[::true]) ->
 VM.find 7750(top_environment observed)=Some(Gval(Fuint 32)instruction) ->
 N.land(to_N instruction)(reference_instruction_mask (rf_compare_class unsigned))=reference_instruction_code (rf_compare_class unsigned) ->
 rf_reference_bank_at(top_environment observed)bank ->
 ref_write_effect(top_environment observed)=RFWrite(to_nat(rf_instruction_rd instruction))(cycle_compare_semantics unsigned bank instruction).
Proof.
 intros Observe Legal Reset Enabled Instruction Match Bank.
 assert(Row:(rf_compare_class unsigned<37)%coq_nat)by(destruct unsigned;vm_compute;lia).
 assert(Writes:rf_isa_writes (rf_compare_class unsigned) =true)by(destruct unsigned;reflexivity).
 destruct(rf_destination_class_observed memory inputs k observed instruction (rf_compare_class unsigned) Observe Legal Instruction Enabled Row Match)as[DutRd RefRd].
 rewrite Writes in RefRd. unfold ref_write_effect. rewrite(ref_write_bit_actual _ _ _ Enabled).
 unfold ref_write_destination. rewrite RefRd.
 rewrite(rf_reference_effect_guards_ext (ref_write_guard(top_environment observed))(rf_write_opcode_bit instruction)).
 2:{ intros stage Stage. destruct(rf_write_decoder_certificate stage Stage)as[Bound Node].
 unfold ref_write_guard. rewrite Node. rewrite(ref_write_bit_actual _ _ _ (rf_reference_decoder_observed memory inputs k observed instruction(rf_write_decoder_index stage)Observe Legal Instruction Enabled Bound)). reflexivity. }
 rewrite(rf_reference_class_write_effect instruction (rf_compare_class unsigned) _ _ _ Row Match Writes).
 assert(Permission:rf_reference_permission_value(rf_isa_write_stage (rf_compare_class unsigned))(ref_write_permission(top_environment observed)(rf_isa_write_stage (rf_compare_class unsigned)))=true).
 { destruct unsigned;reflexivity. }
 rewrite Permission(rf_compare_reference_word_active memory inputs k observed instruction unsigned bank Observe Legal Reset Enabled Instruction Match Bank). reflexivity.
Qed.
