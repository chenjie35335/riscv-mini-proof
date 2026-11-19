Require Import ReferenceControlStabilityHistory ReferenceControlNodeCertificates2 RFALUReferenceImmediate RFShiftCycle RFAddReferencePorts.
Require Import ReferenceControlNodeCongruence2 ReferenceRedirectSpine DUTRedirectDecode CoreSocModel ComparisonNodes RFALUData RFScalarControl ReferenceBranchImmediate ReferenceImmediateTypes ReferenceLoadImmediate ReferenceControlExpressions ReferenceInstructionDecode LoadImmediateSemantics ReferenceLoadSemantics.
From Coq Require Import NArith List Lia.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From nbits Require Import NBits.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Local Opaque flat_statements flat_memories generated_modules generated_top.
Lemma rf_shift_i_low_selected inputs path history limit reset time word lane :(lane<3)%coq_nat ->size word=12%nat ->
 (forall t,(t<=limit)%coq_nat ->VM.find 1(history t)=Some(Gval(Fuint 1)[::reset])) ->
 (forall t,(t<limit)%coq_nat ->formal_value_iter(formal_invalid_policy inputs path)flat_memories(history t)false(history t)flat_statements=Some(history(S t))) ->
 (forall t,(200<=t)%coq_nat ->(t<=limit)%coq_nat ->exists v,VM.find 1884(history t)=Some v /\type_of_val v=Gtyp(Fuint 32)) ->
 (500<=time)%coq_nat ->(time<limit)%coq_nat ->VM.find 1707(history time)=Some(Gval(Fuint 1)[::true]) ->
 (forall n,(n<15)%coq_nat ->VM.find(rf_i_low_guard n)(history time)=Some(Gval(Fuint 1)[::Nat.eqb n (Nat.add 3 lane)])) ->
 VM.find(rf_i_low_yes (Nat.add 3 lane))(history time)=Some(Gval(Fuint 12)word) ->
 VM.find 2248(history time)=Some(Gval(Fuint 12)word).
Proof.
 intros Lane Size Resets Steps Source Lower Upper Enabled Guards Raw.
 assert(Selected:VM.find 2246(history time)=Some(Gval(Fuint 12)word)).
 { change(VM.find(rf_i_low_node 14)(history time)=Some(Gval(Fuint 12)word)).
 eapply(immediate_stable_mux_suffix (formal_invalid_policy inputs path)(history time)(history time)15 (Nat.add 3 lane) 12 word 2231 rf_i_low_node rf_i_low_guard rf_i_low_yes);[lia|exact Size| | |exact Guards| | |exact Raw|lia|lia].
 - intros;reflexivity.
 - intros n Bound value Eval. exact(rf_i_low_value n inputs path history limit reset time value Bound Resets Steps Lower Upper Eval).
 - intros n Bound. exact(proj1(rf_i_low_types n _ history limit time Bound Steps Source Lower ltac:(lia))).
 - intros n Bound. exact(proj2(rf_i_low_types n _ history limit time Bound Steps Source Lower ltac:(lia))). }
 assert(Gate:VM.find 2247(history time)=Some(Gval(Fuint 12)word)).
 { eapply(reference_immediate_value_history 60 inputs path history limit reset time);[lia|exact Resets|exact Steps|exact Lower|exact Upper|]. intro site.
 cbn[reference_immediate_expression reference_immediate_expressions nth reference_control_expr_2247 eval_hfexpr_validif_policy eval_href_validif_policy]. rewrite Enabled;cbn;rewrite Selected. apply dut_decode_adapt;exact Size. }
 eapply(reference_immediate_value_history 61 inputs path history limit reset time);[lia|exact Resets|exact Steps|exact Lower|exact Upper|]. intro site;exact Gate.
Qed.
Lemma rf_shift_i_high_selected inputs path history limit reset time word lane :(lane<3)%coq_nat ->size word=32%nat ->
 (forall t,(t<=limit)%coq_nat ->VM.find 1(history t)=Some(Gval(Fuint 1)[::reset])) ->
 (forall t,(t<limit)%coq_nat ->formal_value_iter(formal_invalid_policy inputs path)flat_memories(history t)false(history t)flat_statements=Some(history(S t))) ->
 (forall t,(200<=t)%coq_nat ->(t<=limit)%coq_nat ->exists v,VM.find 1884(history t)=Some v /\type_of_val v=Gtyp(Fuint 32)) ->
 (500<=time)%coq_nat ->(time<limit)%coq_nat ->VM.find 1707(history time)=Some(Gval(Fuint 1)[::true]) ->
 (forall n,(n<27)%coq_nat ->VM.find(rf_i_high_guard n)(history time)=Some(Gval(Fuint 1)[::Nat.eqb n (Nat.add 3 lane)])) ->
 VM.find(rf_i_high_yes (Nat.add 3 lane))(history time)=Some(Gval(Fuint 32)word) ->
 VM.find 2552(history time)=Some(Gval(Fuint 32)word).
Proof.
 intros Lane Size Resets Steps Source Lower Upper Enabled Guards Raw.
 assert(Selected:VM.find 2550(history time)=Some(Gval(Fuint 32)word)).
 { change(VM.find(rf_i_high_node 26)(history time)=Some(Gval(Fuint 32)word)).
 eapply(immediate_stable_mux_suffix (formal_invalid_policy inputs path)(history time)(history time)27 (Nat.add 3 lane) 32 word 2523 rf_i_high_node rf_i_high_guard rf_i_high_yes);[lia|exact Size| | |exact Guards| | |exact Raw|lia|lia].
 - intros;reflexivity.
 - intros n Bound value Eval. exact(rf_i_high_value n inputs path history limit reset time value Bound Resets Steps Lower Upper Eval).
 - intros n Bound. exact(proj1(rf_i_high_types n _ history limit time Bound Steps Source Lower ltac:(lia))).
 - intros n Bound. exact(proj2(rf_i_high_types n _ history limit time Bound Steps Source Lower ltac:(lia))). }
 assert(Gate:VM.find 2551(history time)=Some(Gval(Fuint 32)word)).
 { eapply(reference_immediate_value_history 302 inputs path history limit reset time);[lia|exact Resets|exact Steps|exact Lower|exact Upper|]. intro site.
 cbn[reference_immediate_expression reference_immediate_expressions nth reference_control_expr_2551 eval_hfexpr_validif_policy eval_href_validif_policy]. rewrite Enabled;cbn;rewrite Selected. apply dut_decode_adapt;exact Size. }
 eapply(reference_immediate_value_history 303 inputs path history limit reset time);[lia|exact Resets|exact Steps|exact Lower|exact Upper|]. intro site;exact Gate.
Qed.
Lemma rf_shift_i_raw inputs path history limit reset time instruction lane :(lane<3)%coq_nat ->
 (forall t,(t<=limit)%coq_nat ->VM.find 1(history t)=Some(Gval(Fuint 1)[::reset])) ->
 (forall t,(t<limit)%coq_nat ->formal_value_iter(formal_invalid_policy inputs path)flat_memories(history t)false(history t)flat_statements=Some(history(S t))) ->
 (500<=time)%coq_nat ->(time<limit)%coq_nat ->VM.find 1884(history time)=Some(Gval(Fuint 32)instruction) ->
 VM.find(rf_i_low_yes (Nat.add 3 lane))(history time)=Some(Gval(Fuint 12)(drop 20(take 32 instruction))).
Proof. intros Lane Resets Steps Lower Upper Source.
destruct lane as[|lane]. { eapply(reference_immediate_value_history 35 inputs path history limit reset time);[lia|exact Resets|exact Steps|exact Lower|exact Upper|]. intro site. cbn[reference_immediate_expression reference_immediate_expressions nth reference_control_expr_2222 eval_hfexpr_validif_policy eval_href_validif_policy]. rewrite Source;reflexivity. }
destruct lane as[|lane]. { eapply(reference_immediate_value_history 34 inputs path history limit reset time);[lia|exact Resets|exact Steps|exact Lower|exact Upper|]. intro site. cbn[reference_immediate_expression reference_immediate_expressions nth reference_control_expr_2221 eval_hfexpr_validif_policy eval_href_validif_policy]. rewrite Source;reflexivity. }
destruct lane as[|lane]. { eapply(reference_immediate_value_history 33 inputs path history limit reset time);[lia|exact Resets|exact Steps|exact Lower|exact Upper|]. intro site. cbn[reference_immediate_expression reference_immediate_expressions nth reference_control_expr_2220 eval_hfexpr_validif_policy eval_href_validif_policy]. rewrite Source;reflexivity. }
lia. Qed.
Lemma rf_shift_i_sign inputs path history limit reset time word lane :(lane<3)%coq_nat ->size word=12%nat ->
 (forall t,(t<=limit)%coq_nat ->VM.find 1(history t)=Some(Gval(Fuint 1)[::reset])) ->
 (forall t,(t<limit)%coq_nat ->formal_value_iter(formal_invalid_policy inputs path)flat_memories(history t)false(history t)flat_statements=Some(history(S t))) ->
 (500<=time)%coq_nat ->(time<limit)%coq_nat ->VM.find 2248(history time)=Some(Gval(Fuint 12)word) ->
 VM.find(rf_i_high_yes (Nat.add 3 lane))(history time)=Some(Gval(Fuint 32)(sext_to 32 word)).
Proof. intros Lane Size Resets Steps Lower Upper Low.
destruct lane as[|lane]. {
assert(V0:VM.find 2493(history time)=Some(Gval(Fuint 1)([::msb word]))).
{ rewrite(reference_control_stable_2493_history inputs path history limit reset Resets Steps time(S time)ltac:(lia)ltac:(lia)ltac:(lia)ltac:(lia)). eapply(reference_redirect_ground_step reference_control_2_offsets reference_control_2_nodes 2493 reference_control_expr_2493);[exact reference_control_2_positions|exact reference_control_2_safety|exact reference_control_member_2493| |apply Steps;lia]. intro site. cbn[reference_control_expr_2493 eval_hfexpr_validif_policy eval_href_validif_policy].
rewrite Low. change(Some(Gval(Fuint 1)(drop(12-1)%nat(take 12 word)))=Some(Gval(Fuint 1)[::msb word])). rewrite(reference_load_sign_bit 12 word Size(eq_refl true));reflexivity. }
assert(V1:VM.find 2494(history time)=Some(Gval(Fuint 1)([::msb word]))).
{ rewrite(reference_control_stable_2494_history inputs path history limit reset Resets Steps time(S time)ltac:(lia)ltac:(lia)ltac:(lia)ltac:(lia)). eapply(reference_redirect_ground_step reference_control_2_offsets reference_control_2_nodes 2494 reference_control_expr_2494);[exact reference_control_2_positions|exact reference_control_2_safety|exact reference_control_member_2494| |apply Steps;lia]. intro site. cbn[reference_control_expr_2494 eval_hfexpr_validif_policy eval_href_validif_policy].
rewrite V0;reflexivity. }
assert(V2:VM.find 2495(history time)=Some(Gval(Fuint 20)(nseq 20(msb word)))).
{ eapply(reference_immediate_value_history 258 inputs path history limit reset time);[lia|exact Resets|exact Steps|exact Lower|exact Upper|]. intro site. cbn[reference_immediate_expression reference_immediate_expressions nth reference_control_expr_2495 eval_hfexpr_validif_policy eval_href_validif_policy].
rewrite V1;destruct(msb word);reflexivity. }
assert(V3:VM.find 2496(history time)=Some(Gval(Fuint 32)(sext_to 32 word))).
{ eapply(reference_immediate_value_history 259 inputs path history limit reset time);[lia|exact Resets|exact Steps|exact Lower|exact Upper|]. intro site. cbn[reference_immediate_expression reference_immediate_expressions nth reference_control_expr_2496 eval_hfexpr_validif_policy eval_href_validif_policy].
rewrite V2 Low. unfold eval_binop. rewrite immediate_cat_no_absorbing. cbn. unfold sext_to,sext. rewrite Size;reflexivity. }
exact V3. }
destruct lane as[|lane]. {
assert(V0:VM.find 2489(history time)=Some(Gval(Fuint 1)([::msb word]))).
{ rewrite(reference_control_stable_2489_history inputs path history limit reset Resets Steps time(S time)ltac:(lia)ltac:(lia)ltac:(lia)ltac:(lia)). eapply(reference_redirect_ground_step reference_control_2_offsets reference_control_2_nodes 2489 reference_control_expr_2489);[exact reference_control_2_positions|exact reference_control_2_safety|exact reference_control_member_2489| |apply Steps;lia]. intro site. cbn[reference_control_expr_2489 eval_hfexpr_validif_policy eval_href_validif_policy].
rewrite Low. change(Some(Gval(Fuint 1)(drop(12-1)%nat(take 12 word)))=Some(Gval(Fuint 1)[::msb word])). rewrite(reference_load_sign_bit 12 word Size(eq_refl true));reflexivity. }
assert(V1:VM.find 2490(history time)=Some(Gval(Fuint 1)([::msb word]))).
{ rewrite(reference_control_stable_2490_history inputs path history limit reset Resets Steps time(S time)ltac:(lia)ltac:(lia)ltac:(lia)ltac:(lia)). eapply(reference_redirect_ground_step reference_control_2_offsets reference_control_2_nodes 2490 reference_control_expr_2490);[exact reference_control_2_positions|exact reference_control_2_safety|exact reference_control_member_2490| |apply Steps;lia]. intro site. cbn[reference_control_expr_2490 eval_hfexpr_validif_policy eval_href_validif_policy].
rewrite V0;reflexivity. }
assert(V2:VM.find 2491(history time)=Some(Gval(Fuint 20)(nseq 20(msb word)))).
{ eapply(reference_immediate_value_history 256 inputs path history limit reset time);[lia|exact Resets|exact Steps|exact Lower|exact Upper|]. intro site. cbn[reference_immediate_expression reference_immediate_expressions nth reference_control_expr_2491 eval_hfexpr_validif_policy eval_href_validif_policy].
rewrite V1;destruct(msb word);reflexivity. }
assert(V3:VM.find 2492(history time)=Some(Gval(Fuint 32)(sext_to 32 word))).
{ eapply(reference_immediate_value_history 257 inputs path history limit reset time);[lia|exact Resets|exact Steps|exact Lower|exact Upper|]. intro site. cbn[reference_immediate_expression reference_immediate_expressions nth reference_control_expr_2492 eval_hfexpr_validif_policy eval_href_validif_policy].
rewrite V2 Low. unfold eval_binop. rewrite immediate_cat_no_absorbing. cbn. unfold sext_to,sext. rewrite Size;reflexivity. }
exact V3. }
destruct lane as[|lane]. {
assert(V0:VM.find 2485(history time)=Some(Gval(Fuint 1)([::msb word]))).
{ rewrite(reference_control_stable_2485_history inputs path history limit reset Resets Steps time(S time)ltac:(lia)ltac:(lia)ltac:(lia)ltac:(lia)). eapply(reference_redirect_ground_step reference_control_2_offsets reference_control_2_nodes 2485 reference_control_expr_2485);[exact reference_control_2_positions|exact reference_control_2_safety|exact reference_control_member_2485| |apply Steps;lia]. intro site. cbn[reference_control_expr_2485 eval_hfexpr_validif_policy eval_href_validif_policy].
rewrite Low. change(Some(Gval(Fuint 1)(drop(12-1)%nat(take 12 word)))=Some(Gval(Fuint 1)[::msb word])). rewrite(reference_load_sign_bit 12 word Size(eq_refl true));reflexivity. }
assert(V1:VM.find 2486(history time)=Some(Gval(Fuint 1)([::msb word]))).
{ rewrite(reference_control_stable_2486_history inputs path history limit reset Resets Steps time(S time)ltac:(lia)ltac:(lia)ltac:(lia)ltac:(lia)). eapply(reference_redirect_ground_step reference_control_2_offsets reference_control_2_nodes 2486 reference_control_expr_2486);[exact reference_control_2_positions|exact reference_control_2_safety|exact reference_control_member_2486| |apply Steps;lia]. intro site. cbn[reference_control_expr_2486 eval_hfexpr_validif_policy eval_href_validif_policy].
rewrite V0;reflexivity. }
assert(V2:VM.find 2487(history time)=Some(Gval(Fuint 20)(nseq 20(msb word)))).
{ eapply(reference_immediate_value_history 254 inputs path history limit reset time);[lia|exact Resets|exact Steps|exact Lower|exact Upper|]. intro site. cbn[reference_immediate_expression reference_immediate_expressions nth reference_control_expr_2487 eval_hfexpr_validif_policy eval_href_validif_policy].
rewrite V1;destruct(msb word);reflexivity. }
assert(V3:VM.find 2488(history time)=Some(Gval(Fuint 32)(sext_to 32 word))).
{ eapply(reference_immediate_value_history 255 inputs path history limit reset time);[lia|exact Resets|exact Steps|exact Lower|exact Upper|]. intro site. cbn[reference_immediate_expression reference_immediate_expressions nth reference_control_expr_2488 eval_hfexpr_validif_policy eval_href_validif_policy].
rewrite V2 Low. unfold eval_binop. rewrite immediate_cat_no_absorbing. cbn. unfold sext_to,sext. rewrite Size;reflexivity. }
exact V3. }
lia. Qed.
Theorem rf_shift_i_immediate_history inputs path history limit reset time instruction lane :
 (lane<3)%coq_nat ->size instruction=32%nat ->
 (forall t,(t<=limit)%coq_nat ->VM.find 1(history t)=Some(Gval(Fuint 1)[::reset])) ->
 (forall t,(t<limit)%coq_nat ->formal_value_iter(formal_invalid_policy inputs path)flat_memories(history t)false(history t)flat_statements=Some(history(S t))) ->
 (forall t,(200<=t)%coq_nat ->(t<=limit)%coq_nat ->VM.find 1884(history t)=Some(Gval(Fuint 32)instruction)) ->
 (500<=time)%coq_nat ->(time<limit)%coq_nat ->VM.find 1707(history time)=Some(Gval(Fuint 1)[::true]) ->
 (forall n,(n<15)%coq_nat ->VM.find(rf_i_low_guard n)(history time)=Some(Gval(Fuint 1)[::Nat.eqb n (Nat.add 3 lane)])) ->
 (forall n,(n<27)%coq_nat ->VM.find(rf_i_high_guard n)(history time)=Some(Gval(Fuint 1)[::Nat.eqb n (Nat.add 3 lane)])) ->
 VM.find 2552(history time)=Some(Gval(Fuint 32)(load_i_immediate instruction)).
Proof.
 intros Lane Size Resets Steps Source Lower Upper Enabled LowGuards HighGuards.
 assert(Typed:forall t,(200<=t)%coq_nat ->(t<=limit)%coq_nat ->exists v,VM.find 1884(history t)=Some v /\type_of_val v=Gtyp(Fuint 32)).
 { intros t L U. exists(Gval(Fuint 32)instruction);split;[apply Source;assumption|reflexivity]. }
 assert(RawSize:size(drop 20(take 32 instruction))=12%nat).
 { rewrite size_drop size_take Size;reflexivity. }
 pose proof(rf_shift_i_raw inputs path history limit reset time instruction lane Lane Resets Steps Lower Upper(Source time ltac:(lia)ltac:(lia)))as Raw.
 pose proof(rf_shift_i_low_selected inputs path history limit reset time(drop 20(take 32 instruction))lane Lane RawSize Resets Steps Typed Lower Upper Enabled LowGuards Raw)as Low.
 pose proof(rf_shift_i_sign inputs path history limit reset time(drop 20(take 32 instruction))lane Lane RawSize Resets Steps Lower Upper Low)as Sign.
 exact(rf_shift_i_high_selected inputs path history limit reset time(load_i_immediate instruction)lane Lane(load_i_immediate_size instruction Size)Resets Steps Typed Lower Upper Enabled HighGuards Sign).
Qed.
Require Import RFReferenceNopHistory FormalObservedHistory ObservedJointRegisterConcrete JointUpdateBoundaryHistory FormalLocalHistory LoadTypeCorrespondence.
Theorem rf_shift_immediate_observed memory inputs k observed instruction lane :
 generated_observe memory inputs k=Some observed ->generated_legal_trace memory inputs k ->
 VM.find 1707(top_environment observed)=Some(Gval(Fuint 1)[::true]) ->
 VM.find 7750(top_environment observed)=Some(Gval(Fuint 32)instruction) ->(lane<3)%coq_nat ->
 N.land(to_N instruction)(reference_instruction_mask(rf_shift_class true lane))=reference_instruction_code(rf_shift_class true lane) ->
 VM.find 2552(top_environment observed)=Some(Gval(Fuint 32)(load_i_immediate instruction)).
Proof.
 intros Observe Legal Enabled Instruction Lane Match.
 destruct(rf_reference_operand_context memory inputs k observed instruction(rf_shift_class true lane)Observe Legal Enabled Instruction(rf_shift_class_bound true lane Lane)Match)
 as[Size[reset[history[Last[Resets[Steps[Source[Enable Decode]]]]]]]].
 pose proof(rf_shift_i_immediate_history (generated_observation_input inputs k)nil history 9259 reset 9250 instruction lane Lane Size Resets Steps Source ltac:(vm_compute;lia)ltac:(vm_compute;lia)Enable)as Value.
 assert(Low:forall n,(n<15)%coq_nat ->VM.find(rf_i_low_guard n)(history 9250%nat)=Some(Gval(Fuint 1)[::Nat.eqb n(Nat.add 3 lane)])).
 { intros n Bound. unfold rf_i_low_guard. rewrite(Decode(rf_i_low_decoder n)ltac:(do 15(destruct n as[|n];[cbn[rf_i_low_decoder nth];lia|]);lia)). do 3(destruct lane as[|lane];[do 15(destruct n as[|n];[reflexivity|]);lia|]);lia. }
 assert(High:forall n,(n<27)%coq_nat ->VM.find(rf_i_high_guard n)(history 9250%nat)=Some(Gval(Fuint 1)[::Nat.eqb n(Nat.add 3 lane)])).
 { intros n Bound. unfold rf_i_high_guard. rewrite(Decode(rf_i_high_decoder n)ltac:(do 27(destruct n as[|n];[cbn[rf_i_high_decoder nth];lia|]);lia)). do 3(destruct lane as[|lane];[do 27(destruct n as[|n];[reflexivity|]);lia|]);lia. }
 specialize(Value Low High).
 rewrite(reference_control_stable_2552_history (generated_observation_input inputs k)nil history 9259 reset Resets Steps 9250 9259 ltac:(vm_compute;lia)ltac:(vm_compute;lia)ltac:(vm_compute;lia)ltac:(vm_compute;lia))Last in Value. exact Value.
Qed.
