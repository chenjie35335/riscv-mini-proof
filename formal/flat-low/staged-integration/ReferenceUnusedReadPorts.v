Require Import CoreSocModel ComparisonNodes RFALUData RFScalarControl ReferenceRs1Types ReferenceRs2Types ReferenceLoadRs1 ReferenceStoreRs2 ReferenceLoadImmediate ReferenceImmediateTypes ReferenceInstructionDecode ReferenceControlStabilityHistory ReferenceControlNodeCongruence0 ReferenceControlNodeCongruence2 ReferenceControlNodeCertificates0 ReferenceControlNodeCertificates2 ReferenceControlExpressions ReferenceRedirectSpine RFReadPorts DUTRedirectDecode.
From Coq Require Import NArith List Lia PeanoNat.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From nbits Require Import NBits.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Firrtl_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Local Opaque flat_statements flat_memories generated_modules generated_top.
Require Import RFALUReferencePorts ReferenceImmediatePrefix RFLinkReferenceEffect.
Definition unused_rs1_prefix_guards :seq VarOrder.T := [::2096;2092;2088].
Theorem unused_rs1_history inputs path history limit reset time instruction :
 (forall t,(t<=limit)%coq_nat ->VM.find 1(history t)=Some(Gval(Fuint 1)[::reset])) ->
 (forall t,(t<limit)%coq_nat ->formal_value_iter(formal_invalid_policy inputs path)flat_memories(history t)false(history t)flat_statements=Some(history(S t))) ->
 (forall t,(200<=t)%coq_nat ->(t<=limit)%coq_nat ->VM.find 1884(history t)=Some(Gval(Fuint 32)instruction)) ->
 (500<=time)%coq_nat ->(time<limit)%coq_nat ->VM.find 1707(history time)=Some(Gval(Fuint 1)[::true]) ->
 (forall n,(n<3)%coq_nat ->VM.find(nth 0 unused_rs1_prefix_guards n)(history time)=Some(Gval(Fuint 1)[::false])) ->
 (forall n,(n<42)%coq_nat ->VM.find(rf_alu_rs1_guard n)(history time)=Some(Gval(Fuint 1)[::false])) ->
 VM.find 2145(history time)=Some(Gval(Fuint 5)(zeros 5)).
Proof.
 intros Resets Steps Source Lower Upper Enabled PrefixGuards Guards.
 assert(Typed:forall t,(200<=t)%coq_nat ->(t<=limit)%coq_nat ->exists value,VM.find 1884(history t)=Some value /\type_of_val value=Gtyp(Fuint 32)).
 {intros t L U. exists(Gval(Fuint 32)instruction);split;[apply Source;assumption|reflexivity]. }
 destruct(reference_rs1_types_history _ history limit 200 Steps Typed 122%nat ltac:(vm_compute;lia)time ltac:(cbv[reference_rs1_rank reference_rs1_ranks nth];lia)ltac:(lia))as[other0[Other0 Shape0]].
 assert(V2099:VM.find 2099(history time)=Some(Gval(Fuint 5)(zeros 5))).
 { rewrite(reference_control_stable_2099_history inputs path history limit reset Resets Steps time(S time)ltac:(lia)ltac:(lia)ltac:(lia)ltac:(lia)).
 eapply(reference_redirect_ground_step reference_control_0_offsets reference_control_0_nodes 2099 reference_control_expr_2099);[exact reference_control_0_positions|exact reference_control_0_safety|exact reference_control_member_2099| |apply Steps;lia].
 intro site. cbn[reference_control_expr_2099 eval_hfexpr_validif_policy eval_href_validif_policy].
 pose proof(PrefixGuards 0%nat ltac:(lia))as Guard. change(VM.find 2096(history time)=Some(Gval(Fuint 1)[::false]))in Guard. rewrite Guard. cbn.
 unfold eval_type_of_expr;cbn[type_of_expr' eval_type_of_ref];rewrite Other0;cbn[option_map];rewrite Shape0. reflexivity. }
 destruct(reference_rs1_types_history _ history limit 200 Steps Typed 120%nat ltac:(vm_compute;lia)time ltac:(cbv[reference_rs1_rank reference_rs1_ranks nth];lia)ltac:(lia))as[other1[Other1 Shape1]].
 assert(V2100:VM.find 2100(history time)=Some(Gval(Fuint 5)(zeros 5))).
 { rewrite(reference_control_stable_2100_history inputs path history limit reset Resets Steps time(S time)ltac:(lia)ltac:(lia)ltac:(lia)ltac:(lia)).
 eapply(reference_redirect_ground_step reference_control_0_offsets reference_control_0_nodes 2100 reference_control_expr_2100);[exact reference_control_0_positions|exact reference_control_0_safety|exact reference_control_member_2100| |apply Steps;lia].
 intro site. cbn[reference_control_expr_2100 eval_hfexpr_validif_policy eval_href_validif_policy].
 pose proof(PrefixGuards 1%nat ltac:(lia))as Guard. change(VM.find 2092(history time)=Some(Gval(Fuint 1)[::false]))in Guard. rewrite Guard. cbn.
 rewrite V2099.
 unfold eval_type_of_expr;cbn[type_of_expr' eval_type_of_ref];rewrite Other1;cbn[option_map];rewrite Shape1. reflexivity. }
 destruct(reference_rs1_types_history _ history limit 200 Steps Typed 118%nat ltac:(vm_compute;lia)time ltac:(cbv[reference_rs1_rank reference_rs1_ranks nth];lia)ltac:(lia))as[other2[Other2 Shape2]].
 assert(V2101:VM.find 2101(history time)=Some(Gval(Fuint 5)(zeros 5))).
 { rewrite(reference_control_stable_2101_history inputs path history limit reset Resets Steps time(S time)ltac:(lia)ltac:(lia)ltac:(lia)ltac:(lia)).
 eapply(reference_redirect_ground_step reference_control_0_offsets reference_control_0_nodes 2101 reference_control_expr_2101);[exact reference_control_0_positions|exact reference_control_0_safety|exact reference_control_member_2101| |apply Steps;lia].
 intro site. cbn[reference_control_expr_2101 eval_hfexpr_validif_policy eval_href_validif_policy].
 pose proof(PrefixGuards 2%nat ltac:(lia))as Guard. change(VM.find 2088(history time)=Some(Gval(Fuint 1)[::false]))in Guard. rewrite Guard. cbn.
 rewrite V2100.
 unfold eval_type_of_expr;cbn[type_of_expr' eval_type_of_ref];rewrite Other2;cbn[option_map];rewrite Shape2. reflexivity. }
 assert(Selected:VM.find(rf_alu_rs1_node 41%nat)(history time)=Some(Gval(Fuint 5)(zeros 5))).
 { eapply(immediate_stable_mux_prefix (formal_invalid_policy inputs path)(history time)42 5(zeros 5)2101 rf_alu_rs1_node rf_alu_rs1_guard rf_alu_rs1_yes);[reflexivity| |exact Guards| |exact V2101|lia].
 - intros n Bound value Eval. rewrite(rf_alu_rs1_same n inputs path history limit reset time Bound Resets Steps Lower Upper).
 apply(rf_alu_rs1_step n _ _ _ value Bound Eval);apply Steps;exact Upper.
 - intros n Bound. exact(proj1(rf_alu_rs1_types n _ history limit time Bound Steps Typed Lower ltac:(lia))). }
 assert(Gate:VM.find 2144(history time)=Some(Gval(Fuint 5)(zeros 5))).
 {eapply(rf_alu_rs1_value 15 inputs path history limit reset time);[lia|exact Resets|exact Steps|exact Lower|exact Upper|]. intro site.
 cbn[rf_alu_rs1_aux_expr nth reference_control_expr_2144 eval_hfexpr_validif_policy eval_href_validif_policy]. rewrite Enabled;cbn;rewrite Selected. reflexivity. }
 eapply(rf_alu_rs1_value 16 inputs path history limit reset time);[lia|exact Resets|exact Steps|exact Lower|exact Upper|]. intro site;exact Gate.
Qed.
Definition unused_rs2_prefix_guards :seq VarOrder.T := [::2059;2054;2049].
Theorem unused_rs2_history inputs path history limit reset time instruction :
 (forall t,(t<=limit)%coq_nat ->VM.find 1(history t)=Some(Gval(Fuint 1)[::reset])) ->
 (forall t,(t<limit)%coq_nat ->formal_value_iter(formal_invalid_policy inputs path)flat_memories(history t)false(history t)flat_statements=Some(history(S t))) ->
 (forall t,(200<=t)%coq_nat ->(t<=limit)%coq_nat ->VM.find 1884(history t)=Some(Gval(Fuint 32)instruction)) ->
 (500<=time)%coq_nat ->(time<limit)%coq_nat ->VM.find 1707(history time)=Some(Gval(Fuint 1)[::true]) ->
 (forall n,(n<3)%coq_nat ->VM.find(nth 0 unused_rs2_prefix_guards n)(history time)=Some(Gval(Fuint 1)[::false])) ->
 (forall n,(n<24)%coq_nat ->VM.find(rf_alu_rs2_guard n)(history time)=Some(Gval(Fuint 1)[::false])) ->
 VM.find 2622(history time)=Some(Gval(Fuint 5)(zeros 5)).
Proof.
 intros Resets Steps Source Lower Upper Enabled PrefixGuards Guards.
 assert(Typed:forall t,(200<=t)%coq_nat ->(t<=limit)%coq_nat ->exists value,VM.find 1884(history t)=Some value /\type_of_val value=Gtyp(Fuint 32)).
 {intros t L U. exists(Gval(Fuint 32)instruction);split;[apply Source;assumption|reflexivity]. }
 destruct(reference_rs2_types_history _ history limit 200 Steps Typed 59%nat ltac:(vm_compute;lia)time ltac:(cbv[reference_rs2_rank reference_rs2_ranks nth];lia)ltac:(lia))as[other0[Other0 Shape0]].
 assert(V2594:VM.find 2594(history time)=Some(Gval(Fuint 5)(zeros 5))).
 { rewrite(reference_control_stable_2594_history inputs path history limit reset Resets Steps time(S time)ltac:(lia)ltac:(lia)ltac:(lia)ltac:(lia)).
 eapply(reference_redirect_ground_step reference_control_2_offsets reference_control_2_nodes 2594 reference_control_expr_2594);[exact reference_control_2_positions|exact reference_control_2_safety|exact reference_control_member_2594| |apply Steps;lia].
 intro site. cbn[reference_control_expr_2594 eval_hfexpr_validif_policy eval_href_validif_policy].
 pose proof(PrefixGuards 0%nat ltac:(lia))as Guard. change(VM.find 2059(history time)=Some(Gval(Fuint 1)[::false]))in Guard. rewrite Guard. cbn.
 unfold eval_type_of_expr;cbn[type_of_expr' eval_type_of_ref];rewrite Other0;cbn[option_map];rewrite Shape0. reflexivity. }
 destruct(reference_rs2_types_history _ history limit 200 Steps Typed 58%nat ltac:(vm_compute;lia)time ltac:(cbv[reference_rs2_rank reference_rs2_ranks nth];lia)ltac:(lia))as[other1[Other1 Shape1]].
 assert(V2595:VM.find 2595(history time)=Some(Gval(Fuint 5)(zeros 5))).
 { rewrite(reference_control_stable_2595_history inputs path history limit reset Resets Steps time(S time)ltac:(lia)ltac:(lia)ltac:(lia)ltac:(lia)).
 eapply(reference_redirect_ground_step reference_control_2_offsets reference_control_2_nodes 2595 reference_control_expr_2595);[exact reference_control_2_positions|exact reference_control_2_safety|exact reference_control_member_2595| |apply Steps;lia].
 intro site. cbn[reference_control_expr_2595 eval_hfexpr_validif_policy eval_href_validif_policy].
 pose proof(PrefixGuards 1%nat ltac:(lia))as Guard. change(VM.find 2054(history time)=Some(Gval(Fuint 1)[::false]))in Guard. rewrite Guard. cbn.
 rewrite V2594.
 unfold eval_type_of_expr;cbn[type_of_expr' eval_type_of_ref];rewrite Other1;cbn[option_map];rewrite Shape1. reflexivity. }
 destruct(reference_rs2_types_history _ history limit 200 Steps Typed 57%nat ltac:(vm_compute;lia)time ltac:(cbv[reference_rs2_rank reference_rs2_ranks nth];lia)ltac:(lia))as[other2[Other2 Shape2]].
 assert(V2596:VM.find 2596(history time)=Some(Gval(Fuint 5)(zeros 5))).
 { rewrite(reference_control_stable_2596_history inputs path history limit reset Resets Steps time(S time)ltac:(lia)ltac:(lia)ltac:(lia)ltac:(lia)).
 eapply(reference_redirect_ground_step reference_control_2_offsets reference_control_2_nodes 2596 reference_control_expr_2596);[exact reference_control_2_positions|exact reference_control_2_safety|exact reference_control_member_2596| |apply Steps;lia].
 intro site. cbn[reference_control_expr_2596 eval_hfexpr_validif_policy eval_href_validif_policy].
 pose proof(PrefixGuards 2%nat ltac:(lia))as Guard. change(VM.find 2049(history time)=Some(Gval(Fuint 1)[::false]))in Guard. rewrite Guard. cbn.
 rewrite V2595.
 unfold eval_type_of_expr;cbn[type_of_expr' eval_type_of_ref];rewrite Other2;cbn[option_map];rewrite Shape2. reflexivity. }
 assert(Selected:VM.find(rf_alu_rs2_node 23%nat)(history time)=Some(Gval(Fuint 5)(zeros 5))).
 { eapply(immediate_stable_mux_prefix (formal_invalid_policy inputs path)(history time)24 5(zeros 5)2596 rf_alu_rs2_node rf_alu_rs2_guard rf_alu_rs2_yes);[reflexivity| |exact Guards| |exact V2596|lia].
 - intros n Bound value Eval. rewrite(rf_alu_rs2_same n inputs path history limit reset time Bound Resets Steps Lower Upper).
 apply(rf_alu_rs2_step n _ _ _ value Bound Eval);apply Steps;exact Upper.
 - intros n Bound. exact(proj1(rf_alu_rs2_types n _ history limit time Bound Steps Typed Lower ltac:(lia))). }
 assert(Gate:VM.find 2621(history time)=Some(Gval(Fuint 5)(zeros 5))).
 {eapply(rf_alu_rs2_value 6 inputs path history limit reset time);[lia|exact Resets|exact Steps|exact Lower|exact Upper|]. intro site.
 cbn[rf_alu_rs2_aux_expr nth reference_control_expr_2621 eval_hfexpr_validif_policy eval_href_validif_policy]. rewrite Enabled;cbn;rewrite Selected. reflexivity. }
 eapply(rf_alu_rs2_value 7 inputs path history limit reset time);[lia|exact Resets|exact Steps|exact Lower|exact Upper|]. intro site;exact Gate.
Qed.
