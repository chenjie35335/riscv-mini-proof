Require Import ReferenceControlNodeCongruence2 ReferenceRedirectSpine DUTRedirectDecode CoreSocModel ComparisonNodes RFALUData RFScalarControl ReferenceBranchImmediate ReferenceImmediateTypes ReferenceLoadImmediate ReferenceControlExpressions ReferenceInstructionDecode LoadImmediateSemantics ReferenceLoadSemantics.
From Coq Require Import NArith List Lia.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From nbits Require Import NBits.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Local Opaque flat_statements flat_memories generated_modules generated_top.

Require Import RFALUReferenceImmediate ReferenceImmediatePrefix ReferenceControlStabilityHistory ReferenceControlNodeCertificates2.

Definition alu_i_low_raw lane :VarOrder.T:=nth 0[::2228;2227;2226]lane.

Lemma alu_i_low_prefix inputs path history limit reset time word lane :(lane<3)%coq_nat ->size word=12%nat ->
 (forall t,(t<=limit)%coq_nat ->VM.find 1(history t)=Some(Gval(Fuint 1)[::reset])) ->
 (forall t,(t<limit)%coq_nat ->formal_value_iter(formal_invalid_policy inputs path)flat_memories(history t)false(history t)flat_statements=Some(history(S t))) ->
 (forall t,(200<=t)%coq_nat ->(t<=limit)%coq_nat ->exists v,VM.find 1884(history t)=Some v /\ type_of_val v=Gtyp(Fuint 32)) ->
 (500<=time)%coq_nat ->(time<limit)%coq_nat ->
 (forall n,(n<3)%coq_nat ->VM.find(nth 0[::2096;2092;2088]n)(history time)=Some(Gval(Fuint 1)[::Nat.eqb n lane])) ->
 VM.find(alu_i_low_raw lane)(history time)=Some(Gval(Fuint 12)word) ->
 VM.find 2231(history time)=Some(Gval(Fuint 12)word).
Proof.
 intros Lane Size Resets Steps Source Lower Upper Guards Raw.

destruct lane as[|lane]. {

assert(V0:VM.find 2229(history time)=Some(Gval(Fuint 12)word)).
{ eapply(reference_immediate_value_history 42 inputs path history limit reset time);[lia|exact Resets|exact Steps|exact Lower|exact Upper|]. intro site.

pose proof(Guards 0%nat ltac:(lia))as Guard.

cbn[reference_immediate_expression reference_immediate_expressions nth reference_control_expr_2229 eval_hfexpr_validif_policy eval_href_validif_policy].
change(VM.find 2096(history time)=Some(Gval(Fuint 1)[::true]))in Guard.
change(VM.find 2228(history time)=Some(Gval(Fuint 12)word))in Raw.
rewrite Guard;cbn;rewrite Raw. apply dut_decode_adapt;exact Size. }

assert(V1:VM.find 2230(history time)=Some(Gval(Fuint 12)word)).
{ eapply(reference_immediate_value_history 43 inputs path history limit reset time);[lia|exact Resets|exact Steps|exact Lower|exact Upper|]. intro site.

pose proof(Guards 1%nat ltac:(lia))as Guard.

destruct(reference_immediate_types_history _ history limit 200 Steps Source 40%nat ltac:(lia)time ltac:(cbv[reference_immediate_rank reference_immediate_ranks nth];lia)ltac:(lia))as[other[Other Shape]].

change(eval_hfexpr_validif_policy(isolated_validif_policy(formal_invalid_policy inputs path))site flat_memories reference_control_expr_2230(history time)(history time)=Some(Gval(Fuint 12)word)).

eapply(immediate_selected_mux _ _ _ _ _ _ _ word other false);[exact Size|exact Guard|exact V0|exact Other|exact Shape]. }

assert(V2:VM.find 2231(history time)=Some(Gval(Fuint 12)word)).
{ eapply(reference_immediate_value_history 44 inputs path history limit reset time);[lia|exact Resets|exact Steps|exact Lower|exact Upper|]. intro site.

pose proof(Guards 2%nat ltac:(lia))as Guard.

destruct(reference_immediate_types_history _ history limit 200 Steps Source 39%nat ltac:(lia)time ltac:(cbv[reference_immediate_rank reference_immediate_ranks nth];lia)ltac:(lia))as[other[Other Shape]].

change(eval_hfexpr_validif_policy(isolated_validif_policy(formal_invalid_policy inputs path))site flat_memories reference_control_expr_2231(history time)(history time)=Some(Gval(Fuint 12)word)).

eapply(immediate_selected_mux _ _ _ _ _ _ _ word other false);[exact Size|exact Guard|exact V1|exact Other|exact Shape]. }

exact V2. }

destruct lane as[|lane]. {

assert(V1:VM.find 2230(history time)=Some(Gval(Fuint 12)word)).
{ eapply(reference_immediate_value_history 43 inputs path history limit reset time);[lia|exact Resets|exact Steps|exact Lower|exact Upper|]. intro site.

pose proof(Guards 1%nat ltac:(lia))as Guard.

destruct(reference_immediate_types_history _ history limit 200 Steps Source 42%nat ltac:(lia)time ltac:(cbv[reference_immediate_rank reference_immediate_ranks nth];lia)ltac:(lia))as[other[Other Shape]].

change(eval_hfexpr_validif_policy(isolated_validif_policy(formal_invalid_policy inputs path))site flat_memories reference_control_expr_2230(history time)(history time)=Some(Gval(Fuint 12)word)).

eapply(immediate_selected_mux _ _ _ _ _ _ _ word other true);[exact Size|exact Guard|exact Raw|exact Other|exact Shape]. }

assert(V2:VM.find 2231(history time)=Some(Gval(Fuint 12)word)).
{ eapply(reference_immediate_value_history 44 inputs path history limit reset time);[lia|exact Resets|exact Steps|exact Lower|exact Upper|]. intro site.

pose proof(Guards 2%nat ltac:(lia))as Guard.

destruct(reference_immediate_types_history _ history limit 200 Steps Source 39%nat ltac:(lia)time ltac:(cbv[reference_immediate_rank reference_immediate_ranks nth];lia)ltac:(lia))as[other[Other Shape]].

change(eval_hfexpr_validif_policy(isolated_validif_policy(formal_invalid_policy inputs path))site flat_memories reference_control_expr_2231(history time)(history time)=Some(Gval(Fuint 12)word)).

eapply(immediate_selected_mux _ _ _ _ _ _ _ word other false);[exact Size|exact Guard|exact V1|exact Other|exact Shape]. }

exact V2. }

destruct lane as[|lane]. {

assert(V2:VM.find 2231(history time)=Some(Gval(Fuint 12)word)).
{ eapply(reference_immediate_value_history 44 inputs path history limit reset time);[lia|exact Resets|exact Steps|exact Lower|exact Upper|]. intro site.

pose proof(Guards 2%nat ltac:(lia))as Guard.

destruct(reference_immediate_types_history _ history limit 200 Steps Source 43%nat ltac:(lia)time ltac:(cbv[reference_immediate_rank reference_immediate_ranks nth];lia)ltac:(lia))as[other[Other Shape]].

change(eval_hfexpr_validif_policy(isolated_validif_policy(formal_invalid_policy inputs path))site flat_memories reference_control_expr_2231(history time)(history time)=Some(Gval(Fuint 12)word)).

eapply(immediate_selected_mux _ _ _ _ _ _ _ word other true);[exact Size|exact Guard|exact Raw|exact Other|exact Shape]. }

exact V2. }

lia. Qed.

Lemma alu_i_low_suffix inputs path history limit reset time word :size word=12%nat ->
 (forall t,(t<=limit)%coq_nat ->VM.find 1(history t)=Some(Gval(Fuint 1)[::reset])) ->
 (forall t,(t<limit)%coq_nat ->formal_value_iter(formal_invalid_policy inputs path)flat_memories(history t)false(history t)flat_statements=Some(history(S t))) ->
 (forall t,(200<=t)%coq_nat ->(t<=limit)%coq_nat ->exists v,VM.find 1884(history t)=Some v /\type_of_val v=Gtyp(Fuint 32)) ->
 (500<=time)%coq_nat ->(time<limit)%coq_nat ->VM.find 1707(history time)=Some(Gval(Fuint 1)[::true]) ->
 (forall n,(n<15)%coq_nat ->VM.find(rf_i_low_guard n)(history time)=Some(Gval(Fuint 1)[::false])) ->
 VM.find 2231(history time)=Some(Gval(Fuint 12)word) ->
 VM.find 2248(history time)=Some(Gval(Fuint 12)word).
Proof.
 intros Size Resets Steps Source Lower Upper Enabled Guards Raw.
 assert(Selected:VM.find 2246(history time)=Some(Gval(Fuint 12)word)).
 { change(VM.find(rf_i_low_node 14)(history time)=Some(Gval(Fuint 12)word)).
 eapply(immediate_stable_mux_prefix (formal_invalid_policy inputs path)(history time)15 12 word 2231 rf_i_low_node rf_i_low_guard rf_i_low_yes);[exact Size| |exact Guards| |exact Raw|lia].
 - intros n Bound value Eval. exact(rf_i_low_value n inputs path history limit reset time value Bound Resets Steps Lower Upper Eval).
 - intros n Bound. exact(proj1(rf_i_low_types n _ history limit time Bound Steps Source Lower ltac:(lia))). }
 assert(Gate:VM.find 2247(history time)=Some(Gval(Fuint 12)word)).
 { eapply(reference_immediate_value_history 60 inputs path history limit reset time);[lia|exact Resets|exact Steps|exact Lower|exact Upper|]. intro site.
 cbn[reference_immediate_expression reference_immediate_expressions nth reference_control_expr_2247 eval_hfexpr_validif_policy eval_href_validif_policy]. rewrite Enabled;cbn;rewrite Selected. apply dut_decode_adapt;exact Size. }
 eapply(reference_immediate_value_history 61 inputs path history limit reset time);[lia|exact Resets|exact Steps|exact Lower|exact Upper|]. intro site;exact Gate.
Qed.

Definition alu_i_high_raw lane :VarOrder.T:=nth 0[::2520;2516;2512]lane.

Lemma alu_i_high_prefix inputs path history limit reset time word lane :(lane<3)%coq_nat ->size word=32%nat ->
 (forall t,(t<=limit)%coq_nat ->VM.find 1(history t)=Some(Gval(Fuint 1)[::reset])) ->
 (forall t,(t<limit)%coq_nat ->formal_value_iter(formal_invalid_policy inputs path)flat_memories(history t)false(history t)flat_statements=Some(history(S t))) ->
 (forall t,(200<=t)%coq_nat ->(t<=limit)%coq_nat ->exists v,VM.find 1884(history t)=Some v /\ type_of_val v=Gtyp(Fuint 32)) ->
 (500<=time)%coq_nat ->(time<limit)%coq_nat ->
 (forall n,(n<3)%coq_nat ->VM.find(nth 0[::2096;2092;2088]n)(history time)=Some(Gval(Fuint 1)[::Nat.eqb n lane])) ->
 VM.find(alu_i_high_raw lane)(history time)=Some(Gval(Fuint 32)word) ->
 VM.find 2523(history time)=Some(Gval(Fuint 32)word).
Proof.
 intros Lane Size Resets Steps Source Lower Upper Guards Raw.

destruct lane as[|lane]. {

assert(V0:VM.find 2521(history time)=Some(Gval(Fuint 32)word)).
{ eapply(reference_immediate_value_history 272 inputs path history limit reset time);[lia|exact Resets|exact Steps|exact Lower|exact Upper|]. intro site.

pose proof(Guards 0%nat ltac:(lia))as Guard.

cbn[reference_immediate_expression reference_immediate_expressions nth reference_control_expr_2521 eval_hfexpr_validif_policy eval_href_validif_policy].
change(VM.find 2096(history time)=Some(Gval(Fuint 1)[::true]))in Guard.
change(VM.find 2520(history time)=Some(Gval(Fuint 32)word))in Raw.
rewrite Guard;cbn;rewrite Raw. apply dut_decode_adapt;exact Size. }

assert(V1:VM.find 2522(history time)=Some(Gval(Fuint 32)word)).
{ eapply(reference_immediate_value_history 273 inputs path history limit reset time);[lia|exact Resets|exact Steps|exact Lower|exact Upper|]. intro site.

pose proof(Guards 1%nat ltac:(lia))as Guard.

destruct(reference_immediate_types_history _ history limit 200 Steps Source 269%nat ltac:(lia)time ltac:(cbv[reference_immediate_rank reference_immediate_ranks nth];lia)ltac:(lia))as[other[Other Shape]].

change(eval_hfexpr_validif_policy(isolated_validif_policy(formal_invalid_policy inputs path))site flat_memories reference_control_expr_2522(history time)(history time)=Some(Gval(Fuint 32)word)).

eapply(immediate_selected_mux _ _ _ _ _ _ _ word other false);[exact Size|exact Guard|exact V0|exact Other|exact Shape]. }

assert(V2:VM.find 2523(history time)=Some(Gval(Fuint 32)word)).
{ eapply(reference_immediate_value_history 274 inputs path history limit reset time);[lia|exact Resets|exact Steps|exact Lower|exact Upper|]. intro site.

pose proof(Guards 2%nat ltac:(lia))as Guard.

destruct(reference_immediate_types_history _ history limit 200 Steps Source 267%nat ltac:(lia)time ltac:(cbv[reference_immediate_rank reference_immediate_ranks nth];lia)ltac:(lia))as[other[Other Shape]].

change(eval_hfexpr_validif_policy(isolated_validif_policy(formal_invalid_policy inputs path))site flat_memories reference_control_expr_2523(history time)(history time)=Some(Gval(Fuint 32)word)).

eapply(immediate_selected_mux _ _ _ _ _ _ _ word other false);[exact Size|exact Guard|exact V1|exact Other|exact Shape]. }

exact V2. }

destruct lane as[|lane]. {

assert(V1:VM.find 2522(history time)=Some(Gval(Fuint 32)word)).
{ eapply(reference_immediate_value_history 273 inputs path history limit reset time);[lia|exact Resets|exact Steps|exact Lower|exact Upper|]. intro site.

pose proof(Guards 1%nat ltac:(lia))as Guard.

destruct(reference_immediate_types_history _ history limit 200 Steps Source 272%nat ltac:(lia)time ltac:(cbv[reference_immediate_rank reference_immediate_ranks nth];lia)ltac:(lia))as[other[Other Shape]].

change(eval_hfexpr_validif_policy(isolated_validif_policy(formal_invalid_policy inputs path))site flat_memories reference_control_expr_2522(history time)(history time)=Some(Gval(Fuint 32)word)).

eapply(immediate_selected_mux _ _ _ _ _ _ _ word other true);[exact Size|exact Guard|exact Raw|exact Other|exact Shape]. }

assert(V2:VM.find 2523(history time)=Some(Gval(Fuint 32)word)).
{ eapply(reference_immediate_value_history 274 inputs path history limit reset time);[lia|exact Resets|exact Steps|exact Lower|exact Upper|]. intro site.

pose proof(Guards 2%nat ltac:(lia))as Guard.

destruct(reference_immediate_types_history _ history limit 200 Steps Source 267%nat ltac:(lia)time ltac:(cbv[reference_immediate_rank reference_immediate_ranks nth];lia)ltac:(lia))as[other[Other Shape]].

change(eval_hfexpr_validif_policy(isolated_validif_policy(formal_invalid_policy inputs path))site flat_memories reference_control_expr_2523(history time)(history time)=Some(Gval(Fuint 32)word)).

eapply(immediate_selected_mux _ _ _ _ _ _ _ word other false);[exact Size|exact Guard|exact V1|exact Other|exact Shape]. }

exact V2. }

destruct lane as[|lane]. {

assert(V2:VM.find 2523(history time)=Some(Gval(Fuint 32)word)).
{ eapply(reference_immediate_value_history 274 inputs path history limit reset time);[lia|exact Resets|exact Steps|exact Lower|exact Upper|]. intro site.

pose proof(Guards 2%nat ltac:(lia))as Guard.

destruct(reference_immediate_types_history _ history limit 200 Steps Source 273%nat ltac:(lia)time ltac:(cbv[reference_immediate_rank reference_immediate_ranks nth];lia)ltac:(lia))as[other[Other Shape]].

change(eval_hfexpr_validif_policy(isolated_validif_policy(formal_invalid_policy inputs path))site flat_memories reference_control_expr_2523(history time)(history time)=Some(Gval(Fuint 32)word)).

eapply(immediate_selected_mux _ _ _ _ _ _ _ word other true);[exact Size|exact Guard|exact Raw|exact Other|exact Shape]. }

exact V2. }

lia. Qed.

Lemma alu_i_high_suffix inputs path history limit reset time word :size word=32%nat ->
 (forall t,(t<=limit)%coq_nat ->VM.find 1(history t)=Some(Gval(Fuint 1)[::reset])) ->
 (forall t,(t<limit)%coq_nat ->formal_value_iter(formal_invalid_policy inputs path)flat_memories(history t)false(history t)flat_statements=Some(history(S t))) ->
 (forall t,(200<=t)%coq_nat ->(t<=limit)%coq_nat ->exists v,VM.find 1884(history t)=Some v /\type_of_val v=Gtyp(Fuint 32)) ->
 (500<=time)%coq_nat ->(time<limit)%coq_nat ->VM.find 1707(history time)=Some(Gval(Fuint 1)[::true]) ->
 (forall n,(n<27)%coq_nat ->VM.find(rf_i_high_guard n)(history time)=Some(Gval(Fuint 1)[::false])) ->
 VM.find 2523(history time)=Some(Gval(Fuint 32)word) ->
 VM.find 2552(history time)=Some(Gval(Fuint 32)word).
Proof.
 intros Size Resets Steps Source Lower Upper Enabled Guards Raw.
 assert(Selected:VM.find 2550(history time)=Some(Gval(Fuint 32)word)).
 { change(VM.find(rf_i_high_node 26)(history time)=Some(Gval(Fuint 32)word)).
 eapply(immediate_stable_mux_prefix (formal_invalid_policy inputs path)(history time)27 32 word 2523 rf_i_high_node rf_i_high_guard rf_i_high_yes);[exact Size| |exact Guards| |exact Raw|lia].
 - intros n Bound value Eval. exact(rf_i_high_value n inputs path history limit reset time value Bound Resets Steps Lower Upper Eval).
 - intros n Bound. exact(proj1(rf_i_high_types n _ history limit time Bound Steps Source Lower ltac:(lia))). }
 assert(Gate:VM.find 2551(history time)=Some(Gval(Fuint 32)word)).
 { eapply(reference_immediate_value_history 302 inputs path history limit reset time);[lia|exact Resets|exact Steps|exact Lower|exact Upper|]. intro site.
 cbn[reference_immediate_expression reference_immediate_expressions nth reference_control_expr_2551 eval_hfexpr_validif_policy eval_href_validif_policy]. rewrite Enabled;cbn;rewrite Selected. apply dut_decode_adapt;exact Size. }
 eapply(reference_immediate_value_history 303 inputs path history limit reset time);[lia|exact Resets|exact Steps|exact Lower|exact Upper|]. intro site;exact Gate.
Qed.

Lemma alu_i_raw inputs path history limit reset time instruction lane :(lane<3)%coq_nat ->
 (forall t,(t<=limit)%coq_nat ->VM.find 1(history t)=Some(Gval(Fuint 1)[::reset])) ->
 (forall t,(t<limit)%coq_nat ->formal_value_iter(formal_invalid_policy inputs path)flat_memories(history t)false(history t)flat_statements=Some(history(S t))) ->
 (500<=time)%coq_nat ->(time<limit)%coq_nat ->VM.find 1884(history time)=Some(Gval(Fuint 32)instruction) ->
 VM.find(alu_i_low_raw lane)(history time)=Some(Gval(Fuint 12)(drop 20(take 32 instruction))).
Proof. intros Lane Resets Steps Lower Upper Source.
destruct lane as[|lane]. { eapply(reference_immediate_value_history 41 inputs path history limit reset time);[lia|exact Resets|exact Steps|exact Lower|exact Upper|]. intro site. cbn[reference_immediate_expression reference_immediate_expressions nth reference_control_expr_2228 eval_hfexpr_validif_policy eval_href_validif_policy]. rewrite Source;reflexivity. }
destruct lane as[|lane]. { eapply(reference_immediate_value_history 40 inputs path history limit reset time);[lia|exact Resets|exact Steps|exact Lower|exact Upper|]. intro site. cbn[reference_immediate_expression reference_immediate_expressions nth reference_control_expr_2227 eval_hfexpr_validif_policy eval_href_validif_policy]. rewrite Source;reflexivity. }
destruct lane as[|lane]. { eapply(reference_immediate_value_history 39 inputs path history limit reset time);[lia|exact Resets|exact Steps|exact Lower|exact Upper|]. intro site. cbn[reference_immediate_expression reference_immediate_expressions nth reference_control_expr_2226 eval_hfexpr_validif_policy eval_href_validif_policy]. rewrite Source;reflexivity. }
lia. Qed.

Lemma alu_i_sign inputs path history limit reset time word lane :(lane<3)%coq_nat ->size word=12%nat ->
 (forall t,(t<=limit)%coq_nat ->VM.find 1(history t)=Some(Gval(Fuint 1)[::reset])) ->
 (forall t,(t<limit)%coq_nat ->formal_value_iter(formal_invalid_policy inputs path)flat_memories(history t)false(history t)flat_statements=Some(history(S t))) ->
 (500<=time)%coq_nat ->(time<limit)%coq_nat ->VM.find 2248(history time)=Some(Gval(Fuint 12)word) ->
 VM.find(alu_i_high_raw lane)(history time)=Some(Gval(Fuint 32)(sext_to 32 word)).
Proof. intros Lane Size Resets Steps Lower Upper Low.
destruct lane as[|lane]. {
assert(V0:VM.find 2517(history time)=Some(Gval(Fuint 1)([::msb word]))).
{ rewrite(reference_control_stable_2517_history inputs path history limit reset Resets Steps time(S time)ltac:(lia)ltac:(lia)ltac:(lia)ltac:(lia)). eapply(reference_redirect_ground_step reference_control_2_offsets reference_control_2_nodes 2517 reference_control_expr_2517);[exact reference_control_2_positions|exact reference_control_2_safety|exact reference_control_member_2517| |apply Steps;lia]. intro site. cbn[reference_control_expr_2517 eval_hfexpr_validif_policy eval_href_validif_policy].
rewrite Low. change(Some(Gval(Fuint 1)(drop(12-1)%nat(take 12 word)))=Some(Gval(Fuint 1)[::msb word])). rewrite(reference_load_sign_bit 12 word Size(eq_refl true));reflexivity. }
assert(V1:VM.find 2518(history time)=Some(Gval(Fuint 1)([::msb word]))).
{ rewrite(reference_control_stable_2518_history inputs path history limit reset Resets Steps time(S time)ltac:(lia)ltac:(lia)ltac:(lia)ltac:(lia)). eapply(reference_redirect_ground_step reference_control_2_offsets reference_control_2_nodes 2518 reference_control_expr_2518);[exact reference_control_2_positions|exact reference_control_2_safety|exact reference_control_member_2518| |apply Steps;lia]. intro site. cbn[reference_control_expr_2518 eval_hfexpr_validif_policy eval_href_validif_policy].
rewrite V0;reflexivity. }
assert(V2:VM.find 2519(history time)=Some(Gval(Fuint 20)(nseq 20(msb word)))).
{ eapply(reference_immediate_value_history 270 inputs path history limit reset time);[lia|exact Resets|exact Steps|exact Lower|exact Upper|]. intro site. cbn[reference_immediate_expression reference_immediate_expressions nth reference_control_expr_2519 eval_hfexpr_validif_policy eval_href_validif_policy].
rewrite V1;destruct(msb word);reflexivity. }
assert(V3:VM.find 2520(history time)=Some(Gval(Fuint 32)(sext_to 32 word))).
{ eapply(reference_immediate_value_history 271 inputs path history limit reset time);[lia|exact Resets|exact Steps|exact Lower|exact Upper|]. intro site. cbn[reference_immediate_expression reference_immediate_expressions nth reference_control_expr_2520 eval_hfexpr_validif_policy eval_href_validif_policy].
rewrite V2 Low. unfold eval_binop. rewrite immediate_cat_no_absorbing. cbn. unfold sext_to,sext. rewrite Size;reflexivity. }
exact V3. }
destruct lane as[|lane]. {
assert(V0:VM.find 2513(history time)=Some(Gval(Fuint 1)([::msb word]))).
{ rewrite(reference_control_stable_2513_history inputs path history limit reset Resets Steps time(S time)ltac:(lia)ltac:(lia)ltac:(lia)ltac:(lia)). eapply(reference_redirect_ground_step reference_control_2_offsets reference_control_2_nodes 2513 reference_control_expr_2513);[exact reference_control_2_positions|exact reference_control_2_safety|exact reference_control_member_2513| |apply Steps;lia]. intro site. cbn[reference_control_expr_2513 eval_hfexpr_validif_policy eval_href_validif_policy].
rewrite Low. change(Some(Gval(Fuint 1)(drop(12-1)%nat(take 12 word)))=Some(Gval(Fuint 1)[::msb word])). rewrite(reference_load_sign_bit 12 word Size(eq_refl true));reflexivity. }
assert(V1:VM.find 2514(history time)=Some(Gval(Fuint 1)([::msb word]))).
{ rewrite(reference_control_stable_2514_history inputs path history limit reset Resets Steps time(S time)ltac:(lia)ltac:(lia)ltac:(lia)ltac:(lia)). eapply(reference_redirect_ground_step reference_control_2_offsets reference_control_2_nodes 2514 reference_control_expr_2514);[exact reference_control_2_positions|exact reference_control_2_safety|exact reference_control_member_2514| |apply Steps;lia]. intro site. cbn[reference_control_expr_2514 eval_hfexpr_validif_policy eval_href_validif_policy].
rewrite V0;reflexivity. }
assert(V2:VM.find 2515(history time)=Some(Gval(Fuint 20)(nseq 20(msb word)))).
{ eapply(reference_immediate_value_history 268 inputs path history limit reset time);[lia|exact Resets|exact Steps|exact Lower|exact Upper|]. intro site. cbn[reference_immediate_expression reference_immediate_expressions nth reference_control_expr_2515 eval_hfexpr_validif_policy eval_href_validif_policy].
rewrite V1;destruct(msb word);reflexivity. }
assert(V3:VM.find 2516(history time)=Some(Gval(Fuint 32)(sext_to 32 word))).
{ eapply(reference_immediate_value_history 269 inputs path history limit reset time);[lia|exact Resets|exact Steps|exact Lower|exact Upper|]. intro site. cbn[reference_immediate_expression reference_immediate_expressions nth reference_control_expr_2516 eval_hfexpr_validif_policy eval_href_validif_policy].
rewrite V2 Low. unfold eval_binop. rewrite immediate_cat_no_absorbing. cbn. unfold sext_to,sext. rewrite Size;reflexivity. }
exact V3. }
destruct lane as[|lane]. {
assert(V0:VM.find 2509(history time)=Some(Gval(Fuint 1)([::msb word]))).
{ rewrite(reference_control_stable_2509_history inputs path history limit reset Resets Steps time(S time)ltac:(lia)ltac:(lia)ltac:(lia)ltac:(lia)). eapply(reference_redirect_ground_step reference_control_2_offsets reference_control_2_nodes 2509 reference_control_expr_2509);[exact reference_control_2_positions|exact reference_control_2_safety|exact reference_control_member_2509| |apply Steps;lia]. intro site. cbn[reference_control_expr_2509 eval_hfexpr_validif_policy eval_href_validif_policy].
rewrite Low. change(Some(Gval(Fuint 1)(drop(12-1)%nat(take 12 word)))=Some(Gval(Fuint 1)[::msb word])). rewrite(reference_load_sign_bit 12 word Size(eq_refl true));reflexivity. }
assert(V1:VM.find 2510(history time)=Some(Gval(Fuint 1)([::msb word]))).
{ rewrite(reference_control_stable_2510_history inputs path history limit reset Resets Steps time(S time)ltac:(lia)ltac:(lia)ltac:(lia)ltac:(lia)). eapply(reference_redirect_ground_step reference_control_2_offsets reference_control_2_nodes 2510 reference_control_expr_2510);[exact reference_control_2_positions|exact reference_control_2_safety|exact reference_control_member_2510| |apply Steps;lia]. intro site. cbn[reference_control_expr_2510 eval_hfexpr_validif_policy eval_href_validif_policy].
rewrite V0;reflexivity. }
assert(V2:VM.find 2511(history time)=Some(Gval(Fuint 20)(nseq 20(msb word)))).
{ eapply(reference_immediate_value_history 266 inputs path history limit reset time);[lia|exact Resets|exact Steps|exact Lower|exact Upper|]. intro site. cbn[reference_immediate_expression reference_immediate_expressions nth reference_control_expr_2511 eval_hfexpr_validif_policy eval_href_validif_policy].
rewrite V1;destruct(msb word);reflexivity. }
assert(V3:VM.find 2512(history time)=Some(Gval(Fuint 32)(sext_to 32 word))).
{ eapply(reference_immediate_value_history 267 inputs path history limit reset time);[lia|exact Resets|exact Steps|exact Lower|exact Upper|]. intro site. cbn[reference_immediate_expression reference_immediate_expressions nth reference_control_expr_2512 eval_hfexpr_validif_policy eval_href_validif_policy].
rewrite V2 Low. unfold eval_binop. rewrite immediate_cat_no_absorbing. cbn. unfold sext_to,sext. rewrite Size;reflexivity. }
exact V3. }
lia. Qed.

Theorem alu_i_immediate_history inputs path history limit reset time instruction lane :
 (lane<3)%coq_nat ->size instruction=32%nat ->
 (forall t,(t<=limit)%coq_nat ->VM.find 1(history t)=Some(Gval(Fuint 1)[::reset])) ->
 (forall t,(t<limit)%coq_nat ->formal_value_iter(formal_invalid_policy inputs path)flat_memories(history t)false(history t)flat_statements=Some(history(S t))) ->
 (forall t,(200<=t)%coq_nat ->(t<=limit)%coq_nat ->VM.find 1884(history t)=Some(Gval(Fuint 32)instruction)) ->
 (500<=time)%coq_nat ->(time<limit)%coq_nat ->VM.find 1707(history time)=Some(Gval(Fuint 1)[::true]) ->
 (forall n,(n<3)%coq_nat ->VM.find(nth 0[::2096;2092;2088]n)(history time)=Some(Gval(Fuint 1)[::Nat.eqb n lane])) ->
 (forall n,(n<15)%coq_nat ->VM.find(rf_i_low_guard n)(history time)=Some(Gval(Fuint 1)[::false])) ->
 (forall n,(n<27)%coq_nat ->VM.find(rf_i_high_guard n)(history time)=Some(Gval(Fuint 1)[::false])) ->
 VM.find 2552(history time)=Some(Gval(Fuint 32)(load_i_immediate instruction)).
Proof.
 intros Lane Size Resets Steps Source Lower Upper Enabled PrefixGuards LowGuards HighGuards.
 assert(Typed:forall t,(200<=t)%coq_nat ->(t<=limit)%coq_nat ->exists v,VM.find 1884(history t)=Some v /\type_of_val v=Gtyp(Fuint 32)).
 { intros t L U. exists(Gval(Fuint 32)instruction);split;[apply Source;assumption|reflexivity]. }
 assert(RawSize:size(drop 20(take 32 instruction))=12%nat).
 { rewrite size_drop size_take Size;reflexivity. }
 pose proof(alu_i_raw inputs path history limit reset time instruction lane Lane Resets Steps Lower Upper(Source time ltac:(lia)ltac:(lia)))as Raw.
 pose proof(alu_i_low_prefix inputs path history limit reset time(drop 20(take 32 instruction))lane Lane RawSize Resets Steps Typed Lower Upper PrefixGuards Raw)as PrefixLow.
 pose proof(alu_i_low_suffix inputs path history limit reset time(drop 20(take 32 instruction))RawSize Resets Steps Typed Lower Upper Enabled LowGuards PrefixLow)as Low.
 pose proof(alu_i_sign inputs path history limit reset time(drop 20(take 32 instruction))lane Lane RawSize Resets Steps Lower Upper Low)as Sign.
 pose proof(alu_i_high_prefix inputs path history limit reset time(load_i_immediate instruction)lane Lane(load_i_immediate_size instruction Size)Resets Steps Typed Lower Upper PrefixGuards Sign)as PrefixHigh.
 exact(alu_i_high_suffix inputs path history limit reset time(load_i_immediate instruction)(load_i_immediate_size instruction Size)Resets Steps Typed Lower Upper Enabled HighGuards PrefixHigh).
Qed.

Require Import ReferenceIllegalObserved LoadPipelineClassification FormalInstructionResetConstants RFReferenceNopHistory FormalObservedHistory ObservedJointRegisterConcrete JointUpdateBoundaryHistory FormalLocalHistory MemoryRequestObservedSemantics LoadTypeCorrespondence.

Lemma alu_i_low_decode instruction lane n :(lane<3)%coq_nat ->(n<15)%coq_nat ->
 N.land(to_N instruction)(reference_instruction_mask lane)=reference_instruction_code lane ->
 N.eqb(reference_instruction_code(rf_i_low_decoder n))(N.land(to_N instruction)(reference_instruction_mask(rf_i_low_decoder n)))=false.
Proof. intros Lane Bound Match.
 rewrite(rf_reference_decode_onehot instruction lane(rf_i_low_decoder n)ltac:(lia)ltac:(do 15(destruct n as[|n];[vm_compute;lia|]);lia)Match).
 do 3(destruct lane as[|lane];[do 15(destruct n as[|n];[reflexivity|]);lia|]);lia.
Qed.

Lemma alu_i_high_decode instruction lane n :(lane<3)%coq_nat ->(n<27)%coq_nat ->
 N.land(to_N instruction)(reference_instruction_mask lane)=reference_instruction_code lane ->
 N.eqb(reference_instruction_code(rf_i_high_decoder n))(N.land(to_N instruction)(reference_instruction_mask(rf_i_high_decoder n)))=false.
Proof. intros Lane Bound Match.
 rewrite(rf_reference_decode_onehot instruction lane(rf_i_high_decoder n)ltac:(lia)ltac:(do 27(destruct n as[|n];[vm_compute;lia|]);lia)Match).
 do 3(destruct lane as[|lane];[do 27(destruct n as[|n];[reflexivity|]);lia|]);lia.
Qed.

Theorem reference_alu_i_immediate_active_observed memory inputs k observed instruction lane :
 generated_observe memory inputs k=Some observed ->generated_legal_trace memory inputs k ->
 VM.find 1(formal_external_inputs(generated_observation_input inputs k))=Some(Gval(Fuint 1)[::false]) ->
 VM.find 1707(top_environment observed)=Some(Gval(Fuint 1)[::true]) ->
 (lane<3)%coq_nat ->VM.find 7750(top_environment observed)=Some(Gval(Fuint 32)instruction) ->
 N.land(to_N instruction)(reference_instruction_mask lane)=reference_instruction_code lane ->
 VM.find 2552(top_environment observed)=Some(Gval(Fuint 32)(load_i_immediate instruction)).
Proof.
 intros Observe Legal Reset Enabled Lane Instruction Match.
 destruct(observed_joint_register_concrete memory inputs k observed 7750%nat 32%nat Observe Legal load_type_instruction_member)as[word[Size Word]]. rewrite Instruction in Word;inversion Word;subst word.
 destruct(observed_history memory inputs k observed Observe Legal)as[reset[history[Last[Steps Resets]]]].
 assert(Inst:forall t,(t<=9259)%coq_nat ->VM.find 7750(history t)=Some(Gval(Fuint 32)instruction)).
 { intros t Upper. pose proof(joint_update_register_history_same _ history 9259 7750 32 load_type_instruction_member Steps)as Hold.
 rewrite(Hold t Upper). rewrite<-(Hold 9259%nat ltac:(lia)). rewrite Last;exact Instruction. }
 assert(Enable:forall t,(195<=t)%coq_nat ->(t<=9259)%coq_nat ->VM.find 1707(history t)=Some(Gval(Fuint 1)[::true])).
 { intros t Lower Upper. rewrite(reference_control_stable_1707_history (generated_observation_input inputs k)nil history 9259 reset Resets Steps t 9259%nat ltac:(lia)ltac:(lia)Upper ltac:(lia))Last;exact Enabled. }
 assert(Source:forall t,(200<=t)%coq_nat ->(t<=9259)%coq_nat ->VM.find 1884(history t)=Some(Gval(Fuint 32)instruction)).
 { intros t Lower Upper. exact(memory_reference_instruction_history _ history 9259 195 instruction true Size Steps Inst Enable t Lower Upper). }
 assert(Decode:forall row,(row<48)%coq_nat ->VM.find(reference_instruction_guard row)(history 9250%nat)=Some(Gval(Fuint 1)[::N.eqb(reference_instruction_code row)(N.land(to_N instruction)(reference_instruction_mask row))])).
 { intros row Row. set(h:=fun t:nat=>history(match t with O=>9248%nat|S O=>9249%nat|_=>9250%nat end)).
 assert(HS:forall t,(t<2)%coq_nat ->formal_value_iter(formal_invalid_policy(generated_observation_input inputs k)nil)flat_memories(h t)false(h t)flat_statements=Some(h(S t))).
 { intros[|[|t]] T;[apply Steps;vm_compute;lia|apply Steps;vm_compute;lia|lia]. }
 assert(HI:forall t,(t<=2)%coq_nat ->VM.find 1884(h t)=Some(Gval(Fuint 32)instruction)).
 { intros[|[|t]] T;unfold h;apply Source;vm_compute;lia. }
 exact(reference_instruction_decode_history _ h 2 instruction row Row HS HI 2 ltac:(lia)ltac:(lia)). }
 assert(Prefix:forall n,(n<3)%coq_nat ->VM.find(nth 0[::2096;2092;2088]n)(history 9250%nat)=Some(Gval(Fuint 1)[::Nat.eqb n lane])).
 { intros n Bound. assert(Id:nth 0[::2096;2092;2088]n=reference_instruction_guard n)by(do 3(destruct n as[|n];[reflexivity|]);lia).
 rewrite Id(Decode n ltac:(lia))(rf_reference_decode_onehot instruction lane n ltac:(lia)ltac:(lia)Match);reflexivity. }
 assert(Low:forall n,(n<15)%coq_nat ->VM.find(rf_i_low_guard n)(history 9250%nat)=Some(Gval(Fuint 1)[::false])).
 { intros n Bound. unfold rf_i_low_guard. rewrite(Decode (rf_i_low_decoder n)ltac:(do 15(destruct n as[|n];[vm_compute;lia|]);lia))(alu_i_low_decode instruction lane n Lane Bound Match);reflexivity. }
 assert(High:forall n,(n<27)%coq_nat ->VM.find(rf_i_high_guard n)(history 9250%nat)=Some(Gval(Fuint 1)[::false])).
 { intros n Bound. unfold rf_i_high_guard. rewrite(Decode (rf_i_high_decoder n)ltac:(do 27(destruct n as[|n];[vm_compute;lia|]);lia))(alu_i_high_decode instruction lane n Lane Bound Match);reflexivity. }
 pose proof(alu_i_immediate_history (generated_observation_input inputs k)nil history 9259 reset 9250 instruction lane Lane Size Resets Steps Source ltac:(vm_compute;lia)ltac:(vm_compute;lia)(Enable 9250%nat ltac:(vm_compute;lia)ltac:(vm_compute;lia))Prefix Low High)as Value.
 rewrite(reference_control_stable_2552_history (generated_observation_input inputs k)nil history 9259 reset Resets Steps 9250 9259 ltac:(vm_compute;lia)ltac:(vm_compute;lia)ltac:(vm_compute;lia)ltac:(vm_compute;lia))Last in Value;exact Value.
Qed.
