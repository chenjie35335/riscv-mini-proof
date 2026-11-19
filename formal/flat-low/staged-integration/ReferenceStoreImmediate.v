Require Import CoreSocModel ComparisonNodes ReferenceLoadImmediate ReferenceImmediateTypes ReferenceLoadSemantics ReferenceRedirectSpine ReferenceControlExpressions ReferenceControlNodeCertificates1 ReferenceControlNodeCongruence1 ReferenceControlStabilityHistory.
From Coq Require Import NArith List Lia.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From nbits Require Import NBits.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Firrtl_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Local Opaque flat_statements flat_memories generated_modules generated_top.
Definition store_imm_aux_node i : VarOrder.T := 2283+N.of_nat i.
Definition store_imm_aux_expression i := nth (@Econst VarOrder.T (Fuint 1) [::false]) [::reference_control_expr_2283;reference_control_expr_2284;reference_control_expr_2285;reference_control_expr_2286;reference_control_expr_2287;reference_control_expr_2288;reference_control_expr_2289;reference_control_expr_2290;reference_control_expr_2291;reference_control_expr_2292;reference_control_expr_2293;reference_control_expr_2294;reference_control_expr_2295;reference_control_expr_2296;reference_control_expr_2297] i.
Theorem store_imm_aux_value i inputs path history limit reset time width word :
 (i < 15)%coq_nat ->
 (forall t, (t <= limit)%coq_nat -> VM.find 1 (history t) = Some (Gval (Fuint 1) [::reset])) ->
 (forall t, (t < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history t) false (history t) flat_statements = Some (history (S t))) ->
 (500 <= time)%coq_nat -> (time < limit)%coq_nat ->
 (forall site, eval_hfexpr_validif_policy (isolated_validif_policy (formal_invalid_policy inputs path)) site flat_memories (store_imm_aux_expression i) (history time) (history time) = Some (Gval (Fuint width) word)) ->
 VM.find (store_imm_aux_node i) (history time) = Some (Gval (Fuint width) word).
Proof.
 intros Bound Resets Steps Lower Upper Eval.
 destruct i as [|i].
 { change (VM.find 2283 (history time) = Some (Gval (Fuint width) word)).
 rewrite (reference_control_stable_2283_history inputs path history limit reset Resets Steps time (S time) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)).
 eapply (reference_redirect_ground_step reference_control_1_offsets reference_control_1_nodes 2283 reference_control_expr_2283);
 [exact reference_control_1_positions|exact reference_control_1_safety|exact reference_control_member_2283|exact Eval|apply Steps;lia]. }
 destruct i as [|i].
 { change (VM.find 2284 (history time) = Some (Gval (Fuint width) word)).
 rewrite (reference_control_stable_2284_history inputs path history limit reset Resets Steps time (S time) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)).
 eapply (reference_redirect_ground_step reference_control_1_offsets reference_control_1_nodes 2284 reference_control_expr_2284);
 [exact reference_control_1_positions|exact reference_control_1_safety|exact reference_control_member_2284|exact Eval|apply Steps;lia]. }
 destruct i as [|i].
 { change (VM.find 2285 (history time) = Some (Gval (Fuint width) word)).
 rewrite (reference_control_stable_2285_history inputs path history limit reset Resets Steps time (S time) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)).
 eapply (reference_redirect_ground_step reference_control_1_offsets reference_control_1_nodes 2285 reference_control_expr_2285);
 [exact reference_control_1_positions|exact reference_control_1_safety|exact reference_control_member_2285|exact Eval|apply Steps;lia]. }
 destruct i as [|i].
 { change (VM.find 2286 (history time) = Some (Gval (Fuint width) word)).
 rewrite (reference_control_stable_2286_history inputs path history limit reset Resets Steps time (S time) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)).
 eapply (reference_redirect_ground_step reference_control_1_offsets reference_control_1_nodes 2286 reference_control_expr_2286);
 [exact reference_control_1_positions|exact reference_control_1_safety|exact reference_control_member_2286|exact Eval|apply Steps;lia]. }
 destruct i as [|i].
 { change (VM.find 2287 (history time) = Some (Gval (Fuint width) word)).
 rewrite (reference_control_stable_2287_history inputs path history limit reset Resets Steps time (S time) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)).
 eapply (reference_redirect_ground_step reference_control_1_offsets reference_control_1_nodes 2287 reference_control_expr_2287);
 [exact reference_control_1_positions|exact reference_control_1_safety|exact reference_control_member_2287|exact Eval|apply Steps;lia]. }
 destruct i as [|i].
 { change (VM.find 2288 (history time) = Some (Gval (Fuint width) word)).
 rewrite (reference_control_stable_2288_history inputs path history limit reset Resets Steps time (S time) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)).
 eapply (reference_redirect_ground_step reference_control_1_offsets reference_control_1_nodes 2288 reference_control_expr_2288);
 [exact reference_control_1_positions|exact reference_control_1_safety|exact reference_control_member_2288|exact Eval|apply Steps;lia]. }
 destruct i as [|i].
 { change (VM.find 2289 (history time) = Some (Gval (Fuint width) word)).
 rewrite (reference_control_stable_2289_history inputs path history limit reset Resets Steps time (S time) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)).
 eapply (reference_redirect_ground_step reference_control_1_offsets reference_control_1_nodes 2289 reference_control_expr_2289);
 [exact reference_control_1_positions|exact reference_control_1_safety|exact reference_control_member_2289|exact Eval|apply Steps;lia]. }
 destruct i as [|i].
 { change (VM.find 2290 (history time) = Some (Gval (Fuint width) word)).
 rewrite (reference_control_stable_2290_history inputs path history limit reset Resets Steps time (S time) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)).
 eapply (reference_redirect_ground_step reference_control_1_offsets reference_control_1_nodes 2290 reference_control_expr_2290);
 [exact reference_control_1_positions|exact reference_control_1_safety|exact reference_control_member_2290|exact Eval|apply Steps;lia]. }
 destruct i as [|i].
 { change (VM.find 2291 (history time) = Some (Gval (Fuint width) word)).
 rewrite (reference_control_stable_2291_history inputs path history limit reset Resets Steps time (S time) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)).
 eapply (reference_redirect_ground_step reference_control_1_offsets reference_control_1_nodes 2291 reference_control_expr_2291);
 [exact reference_control_1_positions|exact reference_control_1_safety|exact reference_control_member_2291|exact Eval|apply Steps;lia]. }
 destruct i as [|i].
 { change (VM.find 2292 (history time) = Some (Gval (Fuint width) word)).
 rewrite (reference_control_stable_2292_history inputs path history limit reset Resets Steps time (S time) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)).
 eapply (reference_redirect_ground_step reference_control_1_offsets reference_control_1_nodes 2292 reference_control_expr_2292);
 [exact reference_control_1_positions|exact reference_control_1_safety|exact reference_control_member_2292|exact Eval|apply Steps;lia]. }
 destruct i as [|i].
 { change (VM.find 2293 (history time) = Some (Gval (Fuint width) word)).
 rewrite (reference_control_stable_2293_history inputs path history limit reset Resets Steps time (S time) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)).
 eapply (reference_redirect_ground_step reference_control_1_offsets reference_control_1_nodes 2293 reference_control_expr_2293);
 [exact reference_control_1_positions|exact reference_control_1_safety|exact reference_control_member_2293|exact Eval|apply Steps;lia]. }
 destruct i as [|i].
 { change (VM.find 2294 (history time) = Some (Gval (Fuint width) word)).
 rewrite (reference_control_stable_2294_history inputs path history limit reset Resets Steps time (S time) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)).
 eapply (reference_redirect_ground_step reference_control_1_offsets reference_control_1_nodes 2294 reference_control_expr_2294);
 [exact reference_control_1_positions|exact reference_control_1_safety|exact reference_control_member_2294|exact Eval|apply Steps;lia]. }
 destruct i as [|i].
 { change (VM.find 2295 (history time) = Some (Gval (Fuint width) word)).
 rewrite (reference_control_stable_2295_history inputs path history limit reset Resets Steps time (S time) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)).
 eapply (reference_redirect_ground_step reference_control_1_offsets reference_control_1_nodes 2295 reference_control_expr_2295);
 [exact reference_control_1_positions|exact reference_control_1_safety|exact reference_control_member_2295|exact Eval|apply Steps;lia]. }
 destruct i as [|i].
 { change (VM.find 2296 (history time) = Some (Gval (Fuint width) word)).
 rewrite (reference_control_stable_2296_history inputs path history limit reset Resets Steps time (S time) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)).
 eapply (reference_redirect_ground_step reference_control_1_offsets reference_control_1_nodes 2296 reference_control_expr_2296);
 [exact reference_control_1_positions|exact reference_control_1_safety|exact reference_control_member_2296|exact Eval|apply Steps;lia]. }
 destruct i as [|i].
 { change (VM.find 2297 (history time) = Some (Gval (Fuint width) word)).
 rewrite (reference_control_stable_2297_history inputs path history limit reset Resets Steps time (S time) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)).
 eapply (reference_redirect_ground_step reference_control_1_offsets reference_control_1_nodes 2297 reference_control_expr_2297);
 [exact reference_control_1_positions|exact reference_control_1_safety|exact reference_control_member_2297|exact Eval|apply Steps;lia]. }
 lia.
Qed.
Theorem store_imm_sign_history lane inputs path history limit reset time low high :
 (lane < 3)%coq_nat -> size low = 5%nat -> size high = 7%nat ->
 (forall t, (t <= limit)%coq_nat -> VM.find 1 (history t) = Some (Gval (Fuint 1) [::reset])) ->
 (forall t, (t < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history t) false (history t) flat_statements = Some (history (S t))) ->
 (500 <= time)%coq_nat -> (time < limit)%coq_nat ->
 VM.find 2268 (history time) = Some (Gval (Fuint 7) high) ->
 VM.find 2282 (history time) = Some (Gval (Fuint 5) low) ->
 VM.find (load_imm_mux_yes true (Nat.sub 7 lane)) (history time) = Some (Gval (Fuint 32) (sext_to 32 (low++high))).
Proof.
 intros Lane LowSize HighSize Resets Steps Lower Upper High Low.
 assert (Size : size (low++high) = 12%nat) by (rewrite size_cat LowSize HighSize;reflexivity).
 destruct lane as [|lane].
 {
 assert (V0 : VM.find 2283 (history time) = Some (Gval (Fuint 12) (low++high))).
 { eapply (store_imm_aux_value 0%nat inputs path history limit reset time);[lia|exact Resets|exact Steps|exact Lower|exact Upper|].
 intro site. cbn [store_imm_aux_expression nth reference_control_expr_2283 eval_hfexpr_validif_policy eval_href_validif_policy].
 rewrite High Low. unfold eval_binop. rewrite immediate_cat_no_absorbing. reflexivity. }
 assert (V1 : VM.find 2284 (history time) = Some (Gval (Fuint 1) ([::msb (low++high)]))).
 { eapply (store_imm_aux_value 1%nat inputs path history limit reset time);[lia|exact Resets|exact Steps|exact Lower|exact Upper|].
 intro site. cbn [store_imm_aux_expression nth reference_control_expr_2284 eval_hfexpr_validif_policy eval_href_validif_policy].
 rewrite V0. change (Some (Gval (Fuint 1) (drop (12-1)%nat (take 12 (low++high)))) = Some (Gval (Fuint 1) [::msb (low++high)])). rewrite (reference_load_sign_bit 12 (low++high) Size (eq_refl true));reflexivity. }
 assert (V2 : VM.find 2285 (history time) = Some (Gval (Fuint 1) ([::msb (low++high)]))).
 { eapply (store_imm_aux_value 2%nat inputs path history limit reset time);[lia|exact Resets|exact Steps|exact Lower|exact Upper|].
 intro site. cbn [store_imm_aux_expression nth reference_control_expr_2285 eval_hfexpr_validif_policy eval_href_validif_policy].
 rewrite V1;destruct (msb (low++high));reflexivity. }
 assert (V3 : VM.find 2286 (history time) = Some (Gval (Fuint 20) (nseq 20 (msb (low++high))))).
 { eapply (store_imm_aux_value 3%nat inputs path history limit reset time);[lia|exact Resets|exact Steps|exact Lower|exact Upper|].
 intro site. cbn [store_imm_aux_expression nth reference_control_expr_2286 eval_hfexpr_validif_policy eval_href_validif_policy].
 rewrite V2;destruct (msb (low++high));reflexivity. }
 assert (V4 : VM.find 2287 (history time) = Some (Gval (Fuint 32) (sext_to 32 (low++high)))).
 { eapply (store_imm_aux_value 4%nat inputs path history limit reset time);[lia|exact Resets|exact Steps|exact Lower|exact Upper|].
 intro site. cbn [store_imm_aux_expression nth reference_control_expr_2287 eval_hfexpr_validif_policy eval_href_validif_policy].
 rewrite V3 V0. unfold eval_binop. rewrite immediate_cat_no_absorbing. cbn. unfold sext_to,sext. rewrite Size. reflexivity. }
 exact V4. }
 destruct lane as [|lane].
 {
 assert (V0 : VM.find 2288 (history time) = Some (Gval (Fuint 12) (low++high))).
 { eapply (store_imm_aux_value 5%nat inputs path history limit reset time);[lia|exact Resets|exact Steps|exact Lower|exact Upper|].
 intro site. cbn [store_imm_aux_expression nth reference_control_expr_2288 eval_hfexpr_validif_policy eval_href_validif_policy].
 rewrite High Low. unfold eval_binop. rewrite immediate_cat_no_absorbing. reflexivity. }
 assert (V1 : VM.find 2289 (history time) = Some (Gval (Fuint 1) ([::msb (low++high)]))).
 { eapply (store_imm_aux_value 6%nat inputs path history limit reset time);[lia|exact Resets|exact Steps|exact Lower|exact Upper|].
 intro site. cbn [store_imm_aux_expression nth reference_control_expr_2289 eval_hfexpr_validif_policy eval_href_validif_policy].
 rewrite V0. change (Some (Gval (Fuint 1) (drop (12-1)%nat (take 12 (low++high)))) = Some (Gval (Fuint 1) [::msb (low++high)])). rewrite (reference_load_sign_bit 12 (low++high) Size (eq_refl true));reflexivity. }
 assert (V2 : VM.find 2290 (history time) = Some (Gval (Fuint 1) ([::msb (low++high)]))).
 { eapply (store_imm_aux_value 7%nat inputs path history limit reset time);[lia|exact Resets|exact Steps|exact Lower|exact Upper|].
 intro site. cbn [store_imm_aux_expression nth reference_control_expr_2290 eval_hfexpr_validif_policy eval_href_validif_policy].
 rewrite V1;destruct (msb (low++high));reflexivity. }
 assert (V3 : VM.find 2291 (history time) = Some (Gval (Fuint 20) (nseq 20 (msb (low++high))))).
 { eapply (store_imm_aux_value 8%nat inputs path history limit reset time);[lia|exact Resets|exact Steps|exact Lower|exact Upper|].
 intro site. cbn [store_imm_aux_expression nth reference_control_expr_2291 eval_hfexpr_validif_policy eval_href_validif_policy].
 rewrite V2;destruct (msb (low++high));reflexivity. }
 assert (V4 : VM.find 2292 (history time) = Some (Gval (Fuint 32) (sext_to 32 (low++high)))).
 { eapply (store_imm_aux_value 9%nat inputs path history limit reset time);[lia|exact Resets|exact Steps|exact Lower|exact Upper|].
 intro site. cbn [store_imm_aux_expression nth reference_control_expr_2292 eval_hfexpr_validif_policy eval_href_validif_policy].
 rewrite V3 V0. unfold eval_binop. rewrite immediate_cat_no_absorbing. cbn. unfold sext_to,sext. rewrite Size. reflexivity. }
 exact V4. }
 destruct lane as [|lane].
 {
 assert (V0 : VM.find 2293 (history time) = Some (Gval (Fuint 12) (low++high))).
 { eapply (store_imm_aux_value 10%nat inputs path history limit reset time);[lia|exact Resets|exact Steps|exact Lower|exact Upper|].
 intro site. cbn [store_imm_aux_expression nth reference_control_expr_2293 eval_hfexpr_validif_policy eval_href_validif_policy].
 rewrite High Low. unfold eval_binop. rewrite immediate_cat_no_absorbing. reflexivity. }
 assert (V1 : VM.find 2294 (history time) = Some (Gval (Fuint 1) ([::msb (low++high)]))).
 { eapply (store_imm_aux_value 11%nat inputs path history limit reset time);[lia|exact Resets|exact Steps|exact Lower|exact Upper|].
 intro site. cbn [store_imm_aux_expression nth reference_control_expr_2294 eval_hfexpr_validif_policy eval_href_validif_policy].
 rewrite V0. change (Some (Gval (Fuint 1) (drop (12-1)%nat (take 12 (low++high)))) = Some (Gval (Fuint 1) [::msb (low++high)])). rewrite (reference_load_sign_bit 12 (low++high) Size (eq_refl true));reflexivity. }
 assert (V2 : VM.find 2295 (history time) = Some (Gval (Fuint 1) ([::msb (low++high)]))).
 { eapply (store_imm_aux_value 12%nat inputs path history limit reset time);[lia|exact Resets|exact Steps|exact Lower|exact Upper|].
 intro site. cbn [store_imm_aux_expression nth reference_control_expr_2295 eval_hfexpr_validif_policy eval_href_validif_policy].
 rewrite V1;destruct (msb (low++high));reflexivity. }
 assert (V3 : VM.find 2296 (history time) = Some (Gval (Fuint 20) (nseq 20 (msb (low++high))))).
 { eapply (store_imm_aux_value 13%nat inputs path history limit reset time);[lia|exact Resets|exact Steps|exact Lower|exact Upper|].
 intro site. cbn [store_imm_aux_expression nth reference_control_expr_2296 eval_hfexpr_validif_policy eval_href_validif_policy].
 rewrite V2;destruct (msb (low++high));reflexivity. }
 assert (V4 : VM.find 2297 (history time) = Some (Gval (Fuint 32) (sext_to 32 (low++high)))).
 { eapply (store_imm_aux_value 14%nat inputs path history limit reset time);[lia|exact Resets|exact Steps|exact Lower|exact Upper|].
 intro site. cbn [store_imm_aux_expression nth reference_control_expr_2297 eval_hfexpr_validif_policy eval_href_validif_policy].
 rewrite V3 V0. unfold eval_binop. rewrite immediate_cat_no_absorbing. cbn. unfold sext_to,sext. rewrite Size. reflexivity. }
 exact V4. }
 lia.
Qed.
(* Store immediate composition. *)
