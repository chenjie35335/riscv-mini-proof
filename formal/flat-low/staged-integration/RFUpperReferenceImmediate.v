Require Import RFUpperSemantics.
Require Import ReferenceControlStabilityHistory ReferenceControlNodeCertificates2 RFALUReferenceImmediate RFShiftCycle RFAddReferencePorts.
Require Import ReferenceControlNodeCongruence2 ReferenceRedirectSpine DUTRedirectDecode CoreSocModel ComparisonNodes RFALUData RFScalarControl ReferenceBranchImmediate ReferenceImmediateTypes ReferenceLoadImmediate ReferenceControlExpressions ReferenceInstructionDecode LoadImmediateSemantics ReferenceLoadSemantics.
From Coq Require Import NArith List Lia.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From nbits Require Import NBits.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Local Opaque flat_statements flat_memories generated_modules generated_top.
Lemma rf_upper_reference_high_selected inputs path history limit reset time word auipc :size word=32%nat ->
 (forall t,(t<=limit)%coq_nat ->VM.find 1(history t)=Some(Gval(Fuint 1)[::reset])) ->
 (forall t,(t<limit)%coq_nat ->formal_value_iter(formal_invalid_policy inputs path)flat_memories(history t)false(history t)flat_statements=Some(history(S t))) ->
 (forall t,(200<=t)%coq_nat ->(t<=limit)%coq_nat ->exists v,VM.find 1884(history t)=Some v /\type_of_val v=Gtyp(Fuint 32)) ->
 (500<=time)%coq_nat ->(time<limit)%coq_nat ->VM.find 1707(history time)=Some(Gval(Fuint 1)[::true]) ->
 (forall n,(n<27)%coq_nat ->VM.find(rf_i_high_guard n)(history time)=Some(Gval(Fuint 1)[::Nat.eqb n (if auipc then 7%nat else 6%nat)])) ->
 VM.find(rf_i_high_yes (if auipc then 7%nat else 6%nat))(history time)=Some(Gval(Fuint 32)word) ->
 VM.find 2552(history time)=Some(Gval(Fuint 32)word).
Proof.
 intros Size Resets Steps Source Lower Upper Enabled Guards Raw.
 assert(Selected:VM.find 2550(history time)=Some(Gval(Fuint 32)word)).
 { change(VM.find(rf_i_high_node 26)(history time)=Some(Gval(Fuint 32)word)).
 eapply(immediate_stable_mux_suffix (formal_invalid_policy inputs path)(history time)(history time)27 (if auipc then 7%nat else 6%nat) 32 word 2523 rf_i_high_node rf_i_high_guard rf_i_high_yes);[destruct auipc;lia|exact Size| | |exact Guards| | |exact Raw|destruct auipc;lia|destruct auipc;lia].
 - intros;reflexivity.
 - intros n Bound value Eval. exact(rf_i_high_value n inputs path history limit reset time value Bound Resets Steps Lower Upper Eval).
 - intros n Bound. exact(proj1(rf_i_high_types n _ history limit time Bound Steps Source Lower ltac:(lia))).
 - intros n Bound. exact(proj2(rf_i_high_types n _ history limit time Bound Steps Source Lower ltac:(lia))). }
 assert(Gate:VM.find 2551(history time)=Some(Gval(Fuint 32)word)).
 { eapply(reference_immediate_value_history 302 inputs path history limit reset time);[lia|exact Resets|exact Steps|exact Lower|exact Upper|]. intro site.
 cbn[reference_immediate_expression reference_immediate_expressions nth reference_control_expr_2551 eval_hfexpr_validif_policy eval_href_validif_policy]. rewrite Enabled;cbn;rewrite Selected. apply dut_decode_adapt;exact Size. }
 eapply(reference_immediate_value_history 303 inputs path history limit reset time);[lia|exact Resets|exact Steps|exact Lower|exact Upper|]. intro site;exact Gate.
Qed.
Theorem rf_upper_reference_immediate_history inputs path history limit reset time instruction auipc :
 size instruction=32%nat ->
 (forall t,(t<=limit)%coq_nat ->VM.find 1(history t)=Some(Gval(Fuint 1)[::reset])) ->
 (forall t,(t<limit)%coq_nat ->formal_value_iter(formal_invalid_policy inputs path)flat_memories(history t)false(history t)flat_statements=Some(history(S t))) ->
 (forall t,(200<=t)%coq_nat ->(t<=limit)%coq_nat ->VM.find 1884(history t)=Some(Gval(Fuint 32)instruction)) ->
 (500<=time)%coq_nat ->(time<limit)%coq_nat ->VM.find 1707(history time)=Some(Gval(Fuint 1)[::true]) ->
 VM.find 2475(history time)=Some(Gval(Fuint 1)[::negb auipc]) ->
 VM.find 2472(history time)=Some(Gval(Fuint 1)[::auipc]) ->
 (forall n,(n<27)%coq_nat ->VM.find(rf_i_high_guard n)(history time)=Some(Gval(Fuint 1)[::Nat.eqb n (if auipc then 7%nat else 6%nat)])) ->
 VM.find 2552(history time)=Some(Gval(Fuint 32)(rf_upper_immediate instruction)).
Proof.
 intros Size Resets Steps Source Lower Upper Enabled Lui Auipc Guards.
 assert(RawSize:size(drop 12(take 32 instruction))=20%nat)by(rewrite size_drop size_take Size;reflexivity).
 assert(ImmSize:size(rf_upper_immediate instruction)=32%nat)by(apply rf_upper_immediate_size;exact Size).
 assert(V2473:VM.find 2473(history time)=Some(Gval(Fuint 20)(drop 12(take 32 instruction)))).
 { eapply(reference_immediate_value_history 244 inputs path history limit reset time);[lia|exact Resets|exact Steps|exact Lower|exact Upper|]. intro site.
 cbn[reference_immediate_expression reference_immediate_expressions nth reference_control_expr_2473 eval_hfexpr_validif_policy eval_href_validif_policy].
 rewrite(Source time ltac:(lia)ltac:(lia));reflexivity. }
 assert(V2476:VM.find 2476(history time)=Some(Gval(Fuint 20)(drop 12(take 32 instruction)))).
 { eapply(reference_immediate_value_history 245 inputs path history limit reset time);[lia|exact Resets|exact Steps|exact Lower|exact Upper|]. intro site.
 cbn[reference_immediate_expression reference_immediate_expressions nth reference_control_expr_2476 eval_hfexpr_validif_policy eval_href_validif_policy].
 rewrite(Source time ltac:(lia)ltac:(lia));reflexivity. }
 assert(V2477:VM.find 2477(history time)=Some(Gval(Fuint 20)(if auipc then zeros 20 else drop 12(take 32 instruction)))).
 { eapply(reference_immediate_value_history 246 inputs path history limit reset time);[lia|exact Resets|exact Steps|exact Lower|exact Upper|]. intro site.
 cbn[reference_immediate_expression reference_immediate_expressions nth reference_control_expr_2477 eval_hfexpr_validif_policy eval_href_validif_policy].
 rewrite Lui. destruct auipc;cbn;unfold eval_type_of_expr;cbn[type_of_expr' eval_type_of_ref];rewrite ?V2476;[reflexivity|apply dut_decode_adapt;exact RawSize]. }
 assert(V2478:VM.find 2478(history time)=Some(Gval(Fuint 20)(drop 12(take 32 instruction)))).
 { eapply(reference_immediate_value_history 247 inputs path history limit reset time);[lia|exact Resets|exact Steps|exact Lower|exact Upper|]. intro site.
 cbn[reference_immediate_expression reference_immediate_expressions nth reference_control_expr_2478 eval_hfexpr_validif_policy eval_href_validif_policy].
 rewrite Auipc. destruct auipc;cbn;unfold eval_type_of_expr;cbn[type_of_expr' eval_type_of_ref];rewrite ?V2473 ?V2477;apply dut_decode_adapt;exact RawSize. }
 assert(V2479:VM.find 2479(history time)=Some(Gval(Fuint 20)(drop 12(take 32 instruction)))).
 { eapply(reference_immediate_value_history 248 inputs path history limit reset time);[lia|exact Resets|exact Steps|exact Lower|exact Upper|]. intro site.
 cbn[reference_immediate_expression reference_immediate_expressions nth reference_control_expr_2479 eval_hfexpr_validif_policy eval_href_validif_policy].
 rewrite Enabled;cbn;rewrite V2478;apply dut_decode_adapt;exact RawSize. }
 assert(V2480:VM.find 2480(history time)=Some(Gval(Fuint 20)(drop 12(take 32 instruction)))).
 { eapply(reference_immediate_value_history 249 inputs path history limit reset time);[lia|exact Resets|exact Steps|exact Lower|exact Upper|]. intro site.
 cbn[reference_immediate_expression reference_immediate_expressions nth reference_control_expr_2480 eval_hfexpr_validif_policy eval_href_validif_policy].
 exact V2479. }
 assert(V2481:VM.find 2481(history time)=Some(Gval(Fuint 32)(rf_upper_immediate instruction))).
 { eapply(reference_immediate_value_history 250 inputs path history limit reset time);[lia|exact Resets|exact Steps|exact Lower|exact Upper|]. intro site.
 cbn[reference_immediate_expression reference_immediate_expressions nth reference_control_expr_2481 eval_hfexpr_validif_policy eval_href_validif_policy].
 rewrite V2480. reflexivity. }
 assert(V2482:VM.find 2482(history time)=Some(Gval(Fuint 32)(rf_upper_immediate instruction))).
 { eapply(reference_immediate_value_history 251 inputs path history limit reset time);[lia|exact Resets|exact Steps|exact Lower|exact Upper|]. intro site.
 cbn[reference_immediate_expression reference_immediate_expressions nth reference_control_expr_2482 eval_hfexpr_validif_policy eval_href_validif_policy].
 rewrite V2481. change(Some(Gval(Fuint 32)(take 32(rf_upper_immediate instruction)))=Some(Gval(Fuint 32)(rf_upper_immediate instruction))). rewrite <-ImmSize. rewrite take_size;reflexivity. }
 assert(V2483:VM.find 2483(history time)=Some(Gval(Fuint 32)(rf_upper_immediate instruction))).
 { eapply(reference_immediate_value_history 252 inputs path history limit reset time);[lia|exact Resets|exact Steps|exact Lower|exact Upper|]. intro site.
 cbn[reference_immediate_expression reference_immediate_expressions nth reference_control_expr_2483 eval_hfexpr_validif_policy eval_href_validif_policy].
 rewrite V2480. reflexivity. }
 assert(V2484:VM.find 2484(history time)=Some(Gval(Fuint 32)(rf_upper_immediate instruction))).
 { eapply(reference_immediate_value_history 253 inputs path history limit reset time);[lia|exact Resets|exact Steps|exact Lower|exact Upper|]. intro site.
 cbn[reference_immediate_expression reference_immediate_expressions nth reference_control_expr_2484 eval_hfexpr_validif_policy eval_href_validif_policy].
 rewrite V2483. change(Some(Gval(Fuint 32)(take 32(rf_upper_immediate instruction)))=Some(Gval(Fuint 32)(rf_upper_immediate instruction))). rewrite <-ImmSize. rewrite take_size;reflexivity. }
 apply(rf_upper_reference_high_selected inputs path history limit reset time(rf_upper_immediate instruction)auipc ImmSize Resets Steps).
 - intros t L U. exists(Gval(Fuint 32)instruction);split;[apply Source;assumption|reflexivity].
 - exact Lower.
 - exact Upper.
 - exact Enabled.
 - exact Guards.
 - destruct auipc;[exact V2482|exact V2484].
Qed.
Require Import RFReferenceNopHistory FormalObservedHistory ObservedJointRegisterConcrete JointUpdateBoundaryHistory FormalLocalHistory LoadTypeCorrespondence.
Theorem rf_upper_reference_immediate_observed memory inputs k observed instruction auipc :
 generated_observe memory inputs k=Some observed ->generated_legal_trace memory inputs k ->
 VM.find 1707(top_environment observed)=Some(Gval(Fuint 1)[::true]) ->
 VM.find 7750(top_environment observed)=Some(Gval(Fuint 32)instruction) ->
 N.land(to_N instruction)(reference_instruction_mask(rf_upper_class auipc))=reference_instruction_code(rf_upper_class auipc) ->
 VM.find 2552(top_environment observed)=Some(Gval(Fuint 32)(rf_upper_immediate instruction)).
Proof.
 intros Observe Legal Enabled Instruction Match.
 destruct(rf_reference_operand_context memory inputs k observed instruction(rf_upper_class auipc)Observe Legal Enabled Instruction(rf_upper_class_bound auipc)Match)
 as[Size[reset[history[Last[Resets[Steps[Source[Enable Decode]]]]]]]].
 assert(Lui:VM.find 2475(history 9250%nat)=Some(Gval(Fuint 1)[::negb auipc])).
 { pose proof(Decode 9%nat ltac:(lia))as D. destruct auipc;exact D. }
 assert(Auipc:VM.find 2472(history 9250%nat)=Some(Gval(Fuint 1)[::auipc])).
 { pose proof(Decode 10%nat ltac:(lia))as D. destruct auipc;exact D. }
 assert(High:forall n,(n<27)%coq_nat ->VM.find(rf_i_high_guard n)(history 9250%nat)=Some(Gval(Fuint 1)[::Nat.eqb n(if auipc then 7%nat else 6%nat)])).
 { intros n Bound. unfold rf_i_high_guard. rewrite(Decode(rf_i_high_decoder n)ltac:(do 27(destruct n as[|n];[cbn[rf_i_high_decoder nth];lia|]);lia)). destruct auipc;do 27(destruct n as[|n];[reflexivity|]);lia. }
 pose proof(rf_upper_reference_immediate_history (generated_observation_input inputs k)nil history 9259 reset 9250 instruction auipc Size Resets Steps Source ltac:(vm_compute;lia)ltac:(vm_compute;lia)Enable Lui Auipc High)as Value.
 rewrite(reference_control_stable_2552_history (generated_observation_input inputs k)nil history 9259 reset Resets Steps 9250 9259 ltac:(vm_compute;lia)ltac:(vm_compute;lia)ltac:(vm_compute;lia)ltac:(vm_compute;lia))Last in Value. exact Value.
Qed.
