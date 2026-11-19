Require Import CoreSocModel ComparisonNodes ReferenceStoreImmediate ReferenceLoadImmediate ReferenceImmediateTypes ReferenceRedirectSpine ReferenceControlExpressions ReferenceControlNodeCertificates0 ReferenceControlNodeCertificates1 ReferenceControlNodeCongruence0 ReferenceControlNodeCongruence1 ReferenceControlStabilityHistory DUTRedirectDecode.
From Coq Require Import NArith List Lia.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From nbits Require Import NBits.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Firrtl_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Local Opaque flat_statements flat_memories generated_modules generated_top.
Definition store_part_node i : VarOrder.T := nth 0 [::1942;1943;1947;1948;1952;1953;2261;2262;2263;2264;2265;2266;2267;2268;2269;2270;2271;2272;2273;2274;2275;2276;2277;2278;2279;2280;2281;2282] i.
Definition store_part_expression i := nth (@Econst VarOrder.T (Fuint 1) [::false]) [::reference_control_expr_1942;reference_control_expr_1943;reference_control_expr_1947;reference_control_expr_1948;reference_control_expr_1952;reference_control_expr_1953;reference_control_expr_2261;reference_control_expr_2262;reference_control_expr_2263;reference_control_expr_2264;reference_control_expr_2265;reference_control_expr_2266;reference_control_expr_2267;reference_control_expr_2268;reference_control_expr_2269;reference_control_expr_2270;reference_control_expr_2271;reference_control_expr_2272;reference_control_expr_2273;reference_control_expr_2274;reference_control_expr_2275;reference_control_expr_2276;reference_control_expr_2277;reference_control_expr_2278;reference_control_expr_2279;reference_control_expr_2280;reference_control_expr_2281;reference_control_expr_2282] i.
Lemma store_part_value i inputs path history limit reset time width word :
 (i < 28)%coq_nat ->
 (forall t, (t <= limit)%coq_nat -> VM.find 1 (history t) = Some (Gval (Fuint 1) [::reset])) ->
 (forall t, (t < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history t) false (history t) flat_statements = Some (history (S t))) ->
 (500 <= time)%coq_nat -> (time < limit)%coq_nat ->
 (forall site, eval_hfexpr_validif_policy (isolated_validif_policy (formal_invalid_policy inputs path)) site flat_memories (store_part_expression i) (history time) (history time) = Some (Gval (Fuint width) word)) ->
 VM.find (store_part_node i) (history time) = Some (Gval (Fuint width) word).
Proof.
 intros Bound Resets Steps Lower Upper Eval.
 destruct i as [|i].
 { change (VM.find 1942 (history time) = Some (Gval (Fuint width) word)).
 rewrite (reference_control_stable_1942_history inputs path history limit reset Resets Steps time (S time) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)).
 eapply (reference_redirect_ground_step reference_control_0_offsets reference_control_0_nodes 1942 reference_control_expr_1942);
 [exact reference_control_0_positions|exact reference_control_0_safety|exact reference_control_member_1942|exact Eval|apply Steps;lia]. }
 destruct i as [|i].
 { change (VM.find 1943 (history time) = Some (Gval (Fuint width) word)).
 rewrite (reference_control_stable_1943_history inputs path history limit reset Resets Steps time (S time) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)).
 eapply (reference_redirect_ground_step reference_control_0_offsets reference_control_0_nodes 1943 reference_control_expr_1943);
 [exact reference_control_0_positions|exact reference_control_0_safety|exact reference_control_member_1943|exact Eval|apply Steps;lia]. }
 destruct i as [|i].
 { change (VM.find 1947 (history time) = Some (Gval (Fuint width) word)).
 rewrite (reference_control_stable_1947_history inputs path history limit reset Resets Steps time (S time) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)).
 eapply (reference_redirect_ground_step reference_control_0_offsets reference_control_0_nodes 1947 reference_control_expr_1947);
 [exact reference_control_0_positions|exact reference_control_0_safety|exact reference_control_member_1947|exact Eval|apply Steps;lia]. }
 destruct i as [|i].
 { change (VM.find 1948 (history time) = Some (Gval (Fuint width) word)).
 rewrite (reference_control_stable_1948_history inputs path history limit reset Resets Steps time (S time) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)).
 eapply (reference_redirect_ground_step reference_control_0_offsets reference_control_0_nodes 1948 reference_control_expr_1948);
 [exact reference_control_0_positions|exact reference_control_0_safety|exact reference_control_member_1948|exact Eval|apply Steps;lia]. }
 destruct i as [|i].
 { change (VM.find 1952 (history time) = Some (Gval (Fuint width) word)).
 rewrite (reference_control_stable_1952_history inputs path history limit reset Resets Steps time (S time) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)).
 eapply (reference_redirect_ground_step reference_control_0_offsets reference_control_0_nodes 1952 reference_control_expr_1952);
 [exact reference_control_0_positions|exact reference_control_0_safety|exact reference_control_member_1952|exact Eval|apply Steps;lia]. }
 destruct i as [|i].
 { change (VM.find 1953 (history time) = Some (Gval (Fuint width) word)).
 rewrite (reference_control_stable_1953_history inputs path history limit reset Resets Steps time (S time) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)).
 eapply (reference_redirect_ground_step reference_control_0_offsets reference_control_0_nodes 1953 reference_control_expr_1953);
 [exact reference_control_0_positions|exact reference_control_0_safety|exact reference_control_member_1953|exact Eval|apply Steps;lia]. }
 destruct i as [|i].
 { change (VM.find 2261 (history time) = Some (Gval (Fuint width) word)).
 rewrite (reference_control_stable_2261_history inputs path history limit reset Resets Steps time (S time) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)).
 eapply (reference_redirect_ground_step reference_control_1_offsets reference_control_1_nodes 2261 reference_control_expr_2261);
 [exact reference_control_1_positions|exact reference_control_1_safety|exact reference_control_member_2261|exact Eval|apply Steps;lia]. }
 destruct i as [|i].
 { change (VM.find 2262 (history time) = Some (Gval (Fuint width) word)).
 rewrite (reference_control_stable_2262_history inputs path history limit reset Resets Steps time (S time) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)).
 eapply (reference_redirect_ground_step reference_control_1_offsets reference_control_1_nodes 2262 reference_control_expr_2262);
 [exact reference_control_1_positions|exact reference_control_1_safety|exact reference_control_member_2262|exact Eval|apply Steps;lia]. }
 destruct i as [|i].
 { change (VM.find 2263 (history time) = Some (Gval (Fuint width) word)).
 rewrite (reference_control_stable_2263_history inputs path history limit reset Resets Steps time (S time) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)).
 eapply (reference_redirect_ground_step reference_control_1_offsets reference_control_1_nodes 2263 reference_control_expr_2263);
 [exact reference_control_1_positions|exact reference_control_1_safety|exact reference_control_member_2263|exact Eval|apply Steps;lia]. }
 destruct i as [|i].
 { change (VM.find 2264 (history time) = Some (Gval (Fuint width) word)).
 rewrite (reference_control_stable_2264_history inputs path history limit reset Resets Steps time (S time) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)).
 eapply (reference_redirect_ground_step reference_control_1_offsets reference_control_1_nodes 2264 reference_control_expr_2264);
 [exact reference_control_1_positions|exact reference_control_1_safety|exact reference_control_member_2264|exact Eval|apply Steps;lia]. }
 destruct i as [|i].
 { change (VM.find 2265 (history time) = Some (Gval (Fuint width) word)).
 rewrite (reference_control_stable_2265_history inputs path history limit reset Resets Steps time (S time) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)).
 eapply (reference_redirect_ground_step reference_control_1_offsets reference_control_1_nodes 2265 reference_control_expr_2265);
 [exact reference_control_1_positions|exact reference_control_1_safety|exact reference_control_member_2265|exact Eval|apply Steps;lia]. }
 destruct i as [|i].
 { change (VM.find 2266 (history time) = Some (Gval (Fuint width) word)).
 rewrite (reference_control_stable_2266_history inputs path history limit reset Resets Steps time (S time) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)).
 eapply (reference_redirect_ground_step reference_control_1_offsets reference_control_1_nodes 2266 reference_control_expr_2266);
 [exact reference_control_1_positions|exact reference_control_1_safety|exact reference_control_member_2266|exact Eval|apply Steps;lia]. }
 destruct i as [|i].
 { change (VM.find 2267 (history time) = Some (Gval (Fuint width) word)).
 rewrite (reference_control_stable_2267_history inputs path history limit reset Resets Steps time (S time) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)).
 eapply (reference_redirect_ground_step reference_control_1_offsets reference_control_1_nodes 2267 reference_control_expr_2267);
 [exact reference_control_1_positions|exact reference_control_1_safety|exact reference_control_member_2267|exact Eval|apply Steps;lia]. }
 destruct i as [|i].
 { change (VM.find 2268 (history time) = Some (Gval (Fuint width) word)).
 rewrite (reference_control_stable_2268_history inputs path history limit reset Resets Steps time (S time) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)).
 eapply (reference_redirect_ground_step reference_control_1_offsets reference_control_1_nodes 2268 reference_control_expr_2268);
 [exact reference_control_1_positions|exact reference_control_1_safety|exact reference_control_member_2268|exact Eval|apply Steps;lia]. }
 destruct i as [|i].
 { change (VM.find 2269 (history time) = Some (Gval (Fuint width) word)).
 rewrite (reference_control_stable_2269_history inputs path history limit reset Resets Steps time (S time) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)).
 eapply (reference_redirect_ground_step reference_control_1_offsets reference_control_1_nodes 2269 reference_control_expr_2269);
 [exact reference_control_1_positions|exact reference_control_1_safety|exact reference_control_member_2269|exact Eval|apply Steps;lia]. }
 destruct i as [|i].
 { change (VM.find 2270 (history time) = Some (Gval (Fuint width) word)).
 rewrite (reference_control_stable_2270_history inputs path history limit reset Resets Steps time (S time) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)).
 eapply (reference_redirect_ground_step reference_control_1_offsets reference_control_1_nodes 2270 reference_control_expr_2270);
 [exact reference_control_1_positions|exact reference_control_1_safety|exact reference_control_member_2270|exact Eval|apply Steps;lia]. }
 destruct i as [|i].
 { change (VM.find 2271 (history time) = Some (Gval (Fuint width) word)).
 rewrite (reference_control_stable_2271_history inputs path history limit reset Resets Steps time (S time) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)).
 eapply (reference_redirect_ground_step reference_control_1_offsets reference_control_1_nodes 2271 reference_control_expr_2271);
 [exact reference_control_1_positions|exact reference_control_1_safety|exact reference_control_member_2271|exact Eval|apply Steps;lia]. }
 destruct i as [|i].
 { change (VM.find 2272 (history time) = Some (Gval (Fuint width) word)).
 rewrite (reference_control_stable_2272_history inputs path history limit reset Resets Steps time (S time) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)).
 eapply (reference_redirect_ground_step reference_control_1_offsets reference_control_1_nodes 2272 reference_control_expr_2272);
 [exact reference_control_1_positions|exact reference_control_1_safety|exact reference_control_member_2272|exact Eval|apply Steps;lia]. }
 destruct i as [|i].
 { change (VM.find 2273 (history time) = Some (Gval (Fuint width) word)).
 rewrite (reference_control_stable_2273_history inputs path history limit reset Resets Steps time (S time) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)).
 eapply (reference_redirect_ground_step reference_control_1_offsets reference_control_1_nodes 2273 reference_control_expr_2273);
 [exact reference_control_1_positions|exact reference_control_1_safety|exact reference_control_member_2273|exact Eval|apply Steps;lia]. }
 destruct i as [|i].
 { change (VM.find 2274 (history time) = Some (Gval (Fuint width) word)).
 rewrite (reference_control_stable_2274_history inputs path history limit reset Resets Steps time (S time) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)).
 eapply (reference_redirect_ground_step reference_control_1_offsets reference_control_1_nodes 2274 reference_control_expr_2274);
 [exact reference_control_1_positions|exact reference_control_1_safety|exact reference_control_member_2274|exact Eval|apply Steps;lia]. }
 destruct i as [|i].
 { change (VM.find 2275 (history time) = Some (Gval (Fuint width) word)).
 rewrite (reference_control_stable_2275_history inputs path history limit reset Resets Steps time (S time) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)).
 eapply (reference_redirect_ground_step reference_control_1_offsets reference_control_1_nodes 2275 reference_control_expr_2275);
 [exact reference_control_1_positions|exact reference_control_1_safety|exact reference_control_member_2275|exact Eval|apply Steps;lia]. }
 destruct i as [|i].
 { change (VM.find 2276 (history time) = Some (Gval (Fuint width) word)).
 rewrite (reference_control_stable_2276_history inputs path history limit reset Resets Steps time (S time) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)).
 eapply (reference_redirect_ground_step reference_control_1_offsets reference_control_1_nodes 2276 reference_control_expr_2276);
 [exact reference_control_1_positions|exact reference_control_1_safety|exact reference_control_member_2276|exact Eval|apply Steps;lia]. }
 destruct i as [|i].
 { change (VM.find 2277 (history time) = Some (Gval (Fuint width) word)).
 rewrite (reference_control_stable_2277_history inputs path history limit reset Resets Steps time (S time) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)).
 eapply (reference_redirect_ground_step reference_control_1_offsets reference_control_1_nodes 2277 reference_control_expr_2277);
 [exact reference_control_1_positions|exact reference_control_1_safety|exact reference_control_member_2277|exact Eval|apply Steps;lia]. }
 destruct i as [|i].
 { change (VM.find 2278 (history time) = Some (Gval (Fuint width) word)).
 rewrite (reference_control_stable_2278_history inputs path history limit reset Resets Steps time (S time) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)).
 eapply (reference_redirect_ground_step reference_control_1_offsets reference_control_1_nodes 2278 reference_control_expr_2278);
 [exact reference_control_1_positions|exact reference_control_1_safety|exact reference_control_member_2278|exact Eval|apply Steps;lia]. }
 destruct i as [|i].
 { change (VM.find 2279 (history time) = Some (Gval (Fuint width) word)).
 rewrite (reference_control_stable_2279_history inputs path history limit reset Resets Steps time (S time) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)).
 eapply (reference_redirect_ground_step reference_control_1_offsets reference_control_1_nodes 2279 reference_control_expr_2279);
 [exact reference_control_1_positions|exact reference_control_1_safety|exact reference_control_member_2279|exact Eval|apply Steps;lia]. }
 destruct i as [|i].
 { change (VM.find 2280 (history time) = Some (Gval (Fuint width) word)).
 rewrite (reference_control_stable_2280_history inputs path history limit reset Resets Steps time (S time) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)).
 eapply (reference_redirect_ground_step reference_control_1_offsets reference_control_1_nodes 2280 reference_control_expr_2280);
 [exact reference_control_1_positions|exact reference_control_1_safety|exact reference_control_member_2280|exact Eval|apply Steps;lia]. }
 destruct i as [|i].
 { change (VM.find 2281 (history time) = Some (Gval (Fuint width) word)).
 rewrite (reference_control_stable_2281_history inputs path history limit reset Resets Steps time (S time) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)).
 eapply (reference_redirect_ground_step reference_control_1_offsets reference_control_1_nodes 2281 reference_control_expr_2281);
 [exact reference_control_1_positions|exact reference_control_1_safety|exact reference_control_member_2281|exact Eval|apply Steps;lia]. }
 destruct i as [|i].
 { change (VM.find 2282 (history time) = Some (Gval (Fuint width) word)).
 rewrite (reference_control_stable_2282_history inputs path history limit reset Resets Steps time (S time) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)).
 eapply (reference_redirect_ground_step reference_control_1_offsets reference_control_1_nodes 2282 reference_control_expr_2282);
 [exact reference_control_1_positions|exact reference_control_1_safety|exact reference_control_member_2282|exact Eval|apply Steps;lia]. }
 lia.
Qed.
Definition store_immediate_low (instruction : bits) := drop 7 (take 12 instruction).
Definition store_immediate_high (instruction : bits) := drop 25 (take 32 instruction).
Theorem store_immediate_parts_history lane inputs path history limit reset time instruction :
 (lane < 3)%coq_nat -> size instruction = 32%nat ->
 (forall t, (t <= limit)%coq_nat -> VM.find 1 (history t) = Some (Gval (Fuint 1) [::reset])) ->
 (forall t, (t < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history t) false (history t) flat_statements = Some (history (S t))) ->
 (500 <= time)%coq_nat -> (time < limit)%coq_nat ->
 VM.find 1884 (history time) = Some (Gval (Fuint 32) instruction) ->
 VM.find 1707 (history time) = Some (Gval (Fuint 1) [::true]) ->
 VM.find 1941 (history time) = Some (Gval (Fuint 1) [::Nat.eqb lane 0]) ->
 VM.find 1946 (history time) = Some (Gval (Fuint 1) [::Nat.eqb lane 1]) ->
 VM.find 1951 (history time) = Some (Gval (Fuint 1) [::Nat.eqb lane 2]) ->
 VM.find 2268 (history time) = Some (Gval (Fuint 7) (store_immediate_high instruction)) /\
 VM.find 2282 (history time) = Some (Gval (Fuint 5) (store_immediate_low instruction)).
Proof.
 intros Lane Size Resets Steps Lower Upper Source Enabled SW SH SB.
 assert (HighSize : size (store_immediate_high instruction) = 7%nat) by (unfold store_immediate_high;rewrite size_drop size_take Size;reflexivity).
 assert (LowSize : size (store_immediate_low instruction) = 5%nat) by (unfold store_immediate_low;rewrite size_drop size_take Size;reflexivity).
 assert (V1942 : VM.find 1942 (history time) = Some (Gval (Fuint 25) (take 25 instruction))).
 { eapply (store_part_value 0 inputs path history limit reset time);[lia|exact Resets|exact Steps|exact Lower|exact Upper|].
 intro site. cbn [store_part_expression nth reference_control_expr_1942 eval_hfexpr_validif_policy eval_href_validif_policy].
 rewrite Source. cbn.
 repeat rewrite drop0. repeat rewrite <- take_min. cbn. reflexivity. }
 assert (V1943 : VM.find 1943 (history time) = Some (Gval (Fuint 20) (take 20 instruction))).
 { eapply (store_part_value 1 inputs path history limit reset time);[lia|exact Resets|exact Steps|exact Lower|exact Upper|].
 intro site. cbn [store_part_expression nth reference_control_expr_1943 eval_hfexpr_validif_policy eval_href_validif_policy].
 rewrite V1942. cbn.
 repeat rewrite drop0. repeat rewrite <- take_min. cbn. reflexivity. }
 assert (V1947 : VM.find 1947 (history time) = Some (Gval (Fuint 25) (take 25 instruction))).
 { eapply (store_part_value 2 inputs path history limit reset time);[lia|exact Resets|exact Steps|exact Lower|exact Upper|].
 intro site. cbn [store_part_expression nth reference_control_expr_1947 eval_hfexpr_validif_policy eval_href_validif_policy].
 rewrite Source. cbn.
 repeat rewrite drop0. repeat rewrite <- take_min. cbn. reflexivity. }
 assert (V1948 : VM.find 1948 (history time) = Some (Gval (Fuint 20) (take 20 instruction))).
 { eapply (store_part_value 3 inputs path history limit reset time);[lia|exact Resets|exact Steps|exact Lower|exact Upper|].
 intro site. cbn [store_part_expression nth reference_control_expr_1948 eval_hfexpr_validif_policy eval_href_validif_policy].
 rewrite V1947. cbn.
 repeat rewrite drop0. repeat rewrite <- take_min. cbn. reflexivity. }
 assert (V1952 : VM.find 1952 (history time) = Some (Gval (Fuint 25) (take 25 instruction))).
 { eapply (store_part_value 4 inputs path history limit reset time);[lia|exact Resets|exact Steps|exact Lower|exact Upper|].
 intro site. cbn [store_part_expression nth reference_control_expr_1952 eval_hfexpr_validif_policy eval_href_validif_policy].
 rewrite Source. cbn.
 repeat rewrite drop0. repeat rewrite <- take_min. cbn. reflexivity. }
 assert (V1953 : VM.find 1953 (history time) = Some (Gval (Fuint 20) (take 20 instruction))).
 { eapply (store_part_value 5 inputs path history limit reset time);[lia|exact Resets|exact Steps|exact Lower|exact Upper|].
 intro site. cbn [store_part_expression nth reference_control_expr_1953 eval_hfexpr_validif_policy eval_href_validif_policy].
 rewrite V1952. cbn.
 repeat rewrite drop0. repeat rewrite <- take_min. cbn. reflexivity. }
 assert (V2261 : VM.find 2261 (history time) = Some (Gval (Fuint 7) (drop 25 (take 32 instruction)))).
 { eapply (store_part_value 6 inputs path history limit reset time);[lia|exact Resets|exact Steps|exact Lower|exact Upper|].
 intro site. cbn [store_part_expression nth reference_control_expr_2261 eval_hfexpr_validif_policy eval_href_validif_policy].
 rewrite Source. cbn.
 repeat rewrite drop0. repeat rewrite <- take_min. cbn. reflexivity. }
 assert (V2262 : VM.find 2262 (history time) = Some (Gval (Fuint 7) (drop 25 (take 32 instruction)))).
 { eapply (store_part_value 7 inputs path history limit reset time);[lia|exact Resets|exact Steps|exact Lower|exact Upper|].
 intro site. cbn [store_part_expression nth reference_control_expr_2262 eval_hfexpr_validif_policy eval_href_validif_policy].
 rewrite Source. cbn.
 repeat rewrite drop0. repeat rewrite <- take_min. cbn. reflexivity. }
 assert (V2263 : VM.find 2263 (history time) = Some (Gval (Fuint 7) (drop 25 (take 32 instruction)))).
 { eapply (store_part_value 8 inputs path history limit reset time);[lia|exact Resets|exact Steps|exact Lower|exact Upper|].
 intro site. cbn [store_part_expression nth reference_control_expr_2263 eval_hfexpr_validif_policy eval_href_validif_policy].
 rewrite Source. cbn.
 repeat rewrite drop0. repeat rewrite <- take_min. cbn. reflexivity. }
 assert (V2269 : VM.find 2269 (history time) = Some (Gval (Fuint 15) (take 15 instruction))).
 { eapply (store_part_value 14 inputs path history limit reset time);[lia|exact Resets|exact Steps|exact Lower|exact Upper|].
 intro site. cbn [store_part_expression nth reference_control_expr_2269 eval_hfexpr_validif_policy eval_href_validif_policy].
 rewrite V1943. cbn.
 repeat rewrite drop0. repeat rewrite <- take_min. cbn. reflexivity. }
 assert (V2270 : VM.find 2270 (history time) = Some (Gval (Fuint 12) (take 12 instruction))).
 { eapply (store_part_value 15 inputs path history limit reset time);[lia|exact Resets|exact Steps|exact Lower|exact Upper|].
 intro site. cbn [store_part_expression nth reference_control_expr_2270 eval_hfexpr_validif_policy eval_href_validif_policy].
 rewrite V2269. cbn.
 repeat rewrite drop0. repeat rewrite <- take_min. cbn. reflexivity. }
 assert (V2271 : VM.find 2271 (history time) = Some (Gval (Fuint 5) (drop 7 (take 12 instruction)))).
 { eapply (store_part_value 16 inputs path history limit reset time);[lia|exact Resets|exact Steps|exact Lower|exact Upper|].
 intro site. cbn [store_part_expression nth reference_control_expr_2271 eval_hfexpr_validif_policy eval_href_validif_policy].
 rewrite V2270. cbn.
 repeat rewrite drop0. repeat rewrite <- take_min. cbn. reflexivity. }
 assert (V2272 : VM.find 2272 (history time) = Some (Gval (Fuint 15) (take 15 instruction))).
 { eapply (store_part_value 17 inputs path history limit reset time);[lia|exact Resets|exact Steps|exact Lower|exact Upper|].
 intro site. cbn [store_part_expression nth reference_control_expr_2272 eval_hfexpr_validif_policy eval_href_validif_policy].
 rewrite V1948. cbn.
 repeat rewrite drop0. repeat rewrite <- take_min. cbn. reflexivity. }
 assert (V2273 : VM.find 2273 (history time) = Some (Gval (Fuint 12) (take 12 instruction))).
 { eapply (store_part_value 18 inputs path history limit reset time);[lia|exact Resets|exact Steps|exact Lower|exact Upper|].
 intro site. cbn [store_part_expression nth reference_control_expr_2273 eval_hfexpr_validif_policy eval_href_validif_policy].
 rewrite V2272. cbn.
 repeat rewrite drop0. repeat rewrite <- take_min. cbn. reflexivity. }
 assert (V2274 : VM.find 2274 (history time) = Some (Gval (Fuint 5) (drop 7 (take 12 instruction)))).
 { eapply (store_part_value 19 inputs path history limit reset time);[lia|exact Resets|exact Steps|exact Lower|exact Upper|].
 intro site. cbn [store_part_expression nth reference_control_expr_2274 eval_hfexpr_validif_policy eval_href_validif_policy].
 rewrite V2273. cbn.
 repeat rewrite drop0. repeat rewrite <- take_min. cbn. reflexivity. }
 assert (V2275 : VM.find 2275 (history time) = Some (Gval (Fuint 15) (take 15 instruction))).
 { eapply (store_part_value 20 inputs path history limit reset time);[lia|exact Resets|exact Steps|exact Lower|exact Upper|].
 intro site. cbn [store_part_expression nth reference_control_expr_2275 eval_hfexpr_validif_policy eval_href_validif_policy].
 rewrite V1953. cbn.
 repeat rewrite drop0. repeat rewrite <- take_min. cbn. reflexivity. }
 assert (V2276 : VM.find 2276 (history time) = Some (Gval (Fuint 12) (take 12 instruction))).
 { eapply (store_part_value 21 inputs path history limit reset time);[lia|exact Resets|exact Steps|exact Lower|exact Upper|].
 intro site. cbn [store_part_expression nth reference_control_expr_2276 eval_hfexpr_validif_policy eval_href_validif_policy].
 rewrite V2275. cbn.
 repeat rewrite drop0. repeat rewrite <- take_min. cbn. reflexivity. }
 assert (V2277 : VM.find 2277 (history time) = Some (Gval (Fuint 5) (drop 7 (take 12 instruction)))).
 { eapply (store_part_value 22 inputs path history limit reset time);[lia|exact Resets|exact Steps|exact Lower|exact Upper|].
 intro site. cbn [store_part_expression nth reference_control_expr_2277 eval_hfexpr_validif_policy eval_href_validif_policy].
 rewrite V2276. cbn.
 repeat rewrite drop0. repeat rewrite <- take_min. cbn. reflexivity. }
 destruct lane as [|lane].
 {
 cbn [Nat.eqb] in SW,SH,SB.
 assert (V2264 : VM.find 2264 (history time) = Some (Gval (Fuint 7) (nseq 7 false))).
 { eapply (store_part_value 9 inputs path history limit reset time);[lia|exact Resets|exact Steps|exact Lower|exact Upper|].
 intro site. cbn [store_part_expression nth reference_control_expr_2264 eval_hfexpr_validif_policy eval_href_validif_policy].
 rewrite SB;cbn. try rewrite V2263.
 unfold eval_type_of_expr;cbn [type_of_expr' eval_type_of_ref];try rewrite V2263.
 change (adapt_hvalue_as_type (Gval (Fuint 7) (nseq 7 false)) (Gtyp (Fuint 7)) = Some (Gval (Fuint 7) (nseq 7 false))). apply dut_decode_adapt. rewrite size_nseq;reflexivity. }
 assert (V2265 : VM.find 2265 (history time) = Some (Gval (Fuint 7) (nseq 7 false))).
 { eapply (store_part_value 10 inputs path history limit reset time);[lia|exact Resets|exact Steps|exact Lower|exact Upper|].
 intro site. cbn [store_part_expression nth reference_control_expr_2265 eval_hfexpr_validif_policy eval_href_validif_policy].
 rewrite SH;cbn. try rewrite V2262;try rewrite V2264.
 unfold eval_type_of_expr;cbn [type_of_expr' eval_type_of_ref];try rewrite V2262;try rewrite V2264.
 change (adapt_hvalue_as_type (Gval (Fuint 7) (nseq 7 false)) (Gtyp (Fuint 7)) = Some (Gval (Fuint 7) (nseq 7 false))). apply dut_decode_adapt. rewrite size_nseq;reflexivity. }
 assert (V2266 : VM.find 2266 (history time) = Some (Gval (Fuint 7) (store_immediate_high instruction))).
 { eapply (store_part_value 11 inputs path history limit reset time);[lia|exact Resets|exact Steps|exact Lower|exact Upper|].
 intro site. cbn [store_part_expression nth reference_control_expr_2266 eval_hfexpr_validif_policy eval_href_validif_policy].
 rewrite SW;cbn. try rewrite V2261;try rewrite V2265.
 unfold eval_type_of_expr;cbn [type_of_expr' eval_type_of_ref];try rewrite V2261;try rewrite V2265.
 change (adapt_hvalue_as_type (Gval (Fuint 7) (store_immediate_high instruction)) (Gtyp (Fuint 7)) = Some (Gval (Fuint 7) (store_immediate_high instruction))). apply dut_decode_adapt. exact HighSize. }
 assert (V2267 : VM.find 2267 (history time) = Some (Gval (Fuint 7) (store_immediate_high instruction))).
 { eapply (store_part_value 12 inputs path history limit reset time);[lia|exact Resets|exact Steps|exact Lower|exact Upper|].
 intro site. cbn [store_part_expression nth reference_control_expr_2267 eval_hfexpr_validif_policy eval_href_validif_policy].
 rewrite Enabled;cbn. try rewrite V2266.
 unfold eval_type_of_expr;cbn [type_of_expr' eval_type_of_ref];try rewrite V2266.
 change (adapt_hvalue_as_type (Gval (Fuint 7) (store_immediate_high instruction)) (Gtyp (Fuint 7)) = Some (Gval (Fuint 7) (store_immediate_high instruction))). apply dut_decode_adapt. exact HighSize. }
 assert (V2268 : VM.find 2268 (history time) = Some (Gval (Fuint 7) (store_immediate_high instruction))).
 { eapply (store_part_value 13 inputs path history limit reset time);[lia|exact Resets|exact Steps|exact Lower|exact Upper|].
 intro site. cbn [store_part_expression nth reference_control_expr_2268 eval_hfexpr_validif_policy eval_href_validif_policy].
 exact V2267. }
 assert (V2278 : VM.find 2278 (history time) = Some (Gval (Fuint 5) (nseq 5 false))).
 { eapply (store_part_value 23 inputs path history limit reset time);[lia|exact Resets|exact Steps|exact Lower|exact Upper|].
 intro site. cbn [store_part_expression nth reference_control_expr_2278 eval_hfexpr_validif_policy eval_href_validif_policy].
 rewrite SB;cbn. try rewrite V2277.
 unfold eval_type_of_expr;cbn [type_of_expr' eval_type_of_ref];try rewrite V2277.
 change (adapt_hvalue_as_type (Gval (Fuint 5) (nseq 5 false)) (Gtyp (Fuint 5)) = Some (Gval (Fuint 5) (nseq 5 false))). apply dut_decode_adapt. rewrite size_nseq;reflexivity. }
 assert (V2279 : VM.find 2279 (history time) = Some (Gval (Fuint 5) (nseq 5 false))).
 { eapply (store_part_value 24 inputs path history limit reset time);[lia|exact Resets|exact Steps|exact Lower|exact Upper|].
 intro site. cbn [store_part_expression nth reference_control_expr_2279 eval_hfexpr_validif_policy eval_href_validif_policy].
 rewrite SH;cbn. try rewrite V2274;try rewrite V2278.
 unfold eval_type_of_expr;cbn [type_of_expr' eval_type_of_ref];try rewrite V2274;try rewrite V2278.
 change (adapt_hvalue_as_type (Gval (Fuint 5) (nseq 5 false)) (Gtyp (Fuint 5)) = Some (Gval (Fuint 5) (nseq 5 false))). apply dut_decode_adapt. rewrite size_nseq;reflexivity. }
 assert (V2280 : VM.find 2280 (history time) = Some (Gval (Fuint 5) (store_immediate_low instruction))).
 { eapply (store_part_value 25 inputs path history limit reset time);[lia|exact Resets|exact Steps|exact Lower|exact Upper|].
 intro site. cbn [store_part_expression nth reference_control_expr_2280 eval_hfexpr_validif_policy eval_href_validif_policy].
 rewrite SW;cbn. try rewrite V2271;try rewrite V2279.
 unfold eval_type_of_expr;cbn [type_of_expr' eval_type_of_ref];try rewrite V2271;try rewrite V2279.
 change (adapt_hvalue_as_type (Gval (Fuint 5) (store_immediate_low instruction)) (Gtyp (Fuint 5)) = Some (Gval (Fuint 5) (store_immediate_low instruction))). apply dut_decode_adapt. exact LowSize. }
 assert (V2281 : VM.find 2281 (history time) = Some (Gval (Fuint 5) (store_immediate_low instruction))).
 { eapply (store_part_value 26 inputs path history limit reset time);[lia|exact Resets|exact Steps|exact Lower|exact Upper|].
 intro site. cbn [store_part_expression nth reference_control_expr_2281 eval_hfexpr_validif_policy eval_href_validif_policy].
 rewrite Enabled;cbn. try rewrite V2280.
 unfold eval_type_of_expr;cbn [type_of_expr' eval_type_of_ref];try rewrite V2280.
 change (adapt_hvalue_as_type (Gval (Fuint 5) (store_immediate_low instruction)) (Gtyp (Fuint 5)) = Some (Gval (Fuint 5) (store_immediate_low instruction))). apply dut_decode_adapt. exact LowSize. }
 assert (V2282 : VM.find 2282 (history time) = Some (Gval (Fuint 5) (store_immediate_low instruction))).
 { eapply (store_part_value 27 inputs path history limit reset time);[lia|exact Resets|exact Steps|exact Lower|exact Upper|].
 intro site. cbn [store_part_expression nth reference_control_expr_2282 eval_hfexpr_validif_policy eval_href_validif_policy].
 exact V2281. }
 split;[exact V2268|exact V2282]. }
 destruct lane as [|lane].
 {
 cbn [Nat.eqb] in SW,SH,SB.
 assert (V2264 : VM.find 2264 (history time) = Some (Gval (Fuint 7) (nseq 7 false))).
 { eapply (store_part_value 9 inputs path history limit reset time);[lia|exact Resets|exact Steps|exact Lower|exact Upper|].
 intro site. cbn [store_part_expression nth reference_control_expr_2264 eval_hfexpr_validif_policy eval_href_validif_policy].
 rewrite SB;cbn. try rewrite V2263.
 unfold eval_type_of_expr;cbn [type_of_expr' eval_type_of_ref];try rewrite V2263.
 change (adapt_hvalue_as_type (Gval (Fuint 7) (nseq 7 false)) (Gtyp (Fuint 7)) = Some (Gval (Fuint 7) (nseq 7 false))). apply dut_decode_adapt. rewrite size_nseq;reflexivity. }
 assert (V2265 : VM.find 2265 (history time) = Some (Gval (Fuint 7) (store_immediate_high instruction))).
 { eapply (store_part_value 10 inputs path history limit reset time);[lia|exact Resets|exact Steps|exact Lower|exact Upper|].
 intro site. cbn [store_part_expression nth reference_control_expr_2265 eval_hfexpr_validif_policy eval_href_validif_policy].
 rewrite SH;cbn. try rewrite V2262;try rewrite V2264.
 unfold eval_type_of_expr;cbn [type_of_expr' eval_type_of_ref];try rewrite V2262;try rewrite V2264.
 change (adapt_hvalue_as_type (Gval (Fuint 7) (store_immediate_high instruction)) (Gtyp (Fuint 7)) = Some (Gval (Fuint 7) (store_immediate_high instruction))). apply dut_decode_adapt. exact HighSize. }
 assert (V2266 : VM.find 2266 (history time) = Some (Gval (Fuint 7) (store_immediate_high instruction))).
 { eapply (store_part_value 11 inputs path history limit reset time);[lia|exact Resets|exact Steps|exact Lower|exact Upper|].
 intro site. cbn [store_part_expression nth reference_control_expr_2266 eval_hfexpr_validif_policy eval_href_validif_policy].
 rewrite SW;cbn. try rewrite V2261;try rewrite V2265.
 unfold eval_type_of_expr;cbn [type_of_expr' eval_type_of_ref];try rewrite V2261;try rewrite V2265.
 change (adapt_hvalue_as_type (Gval (Fuint 7) (store_immediate_high instruction)) (Gtyp (Fuint 7)) = Some (Gval (Fuint 7) (store_immediate_high instruction))). apply dut_decode_adapt. exact HighSize. }
 assert (V2267 : VM.find 2267 (history time) = Some (Gval (Fuint 7) (store_immediate_high instruction))).
 { eapply (store_part_value 12 inputs path history limit reset time);[lia|exact Resets|exact Steps|exact Lower|exact Upper|].
 intro site. cbn [store_part_expression nth reference_control_expr_2267 eval_hfexpr_validif_policy eval_href_validif_policy].
 rewrite Enabled;cbn. try rewrite V2266.
 unfold eval_type_of_expr;cbn [type_of_expr' eval_type_of_ref];try rewrite V2266.
 change (adapt_hvalue_as_type (Gval (Fuint 7) (store_immediate_high instruction)) (Gtyp (Fuint 7)) = Some (Gval (Fuint 7) (store_immediate_high instruction))). apply dut_decode_adapt. exact HighSize. }
 assert (V2268 : VM.find 2268 (history time) = Some (Gval (Fuint 7) (store_immediate_high instruction))).
 { eapply (store_part_value 13 inputs path history limit reset time);[lia|exact Resets|exact Steps|exact Lower|exact Upper|].
 intro site. cbn [store_part_expression nth reference_control_expr_2268 eval_hfexpr_validif_policy eval_href_validif_policy].
 exact V2267. }
 assert (V2278 : VM.find 2278 (history time) = Some (Gval (Fuint 5) (nseq 5 false))).
 { eapply (store_part_value 23 inputs path history limit reset time);[lia|exact Resets|exact Steps|exact Lower|exact Upper|].
 intro site. cbn [store_part_expression nth reference_control_expr_2278 eval_hfexpr_validif_policy eval_href_validif_policy].
 rewrite SB;cbn. try rewrite V2277.
 unfold eval_type_of_expr;cbn [type_of_expr' eval_type_of_ref];try rewrite V2277.
 change (adapt_hvalue_as_type (Gval (Fuint 5) (nseq 5 false)) (Gtyp (Fuint 5)) = Some (Gval (Fuint 5) (nseq 5 false))). apply dut_decode_adapt. rewrite size_nseq;reflexivity. }
 assert (V2279 : VM.find 2279 (history time) = Some (Gval (Fuint 5) (store_immediate_low instruction))).
 { eapply (store_part_value 24 inputs path history limit reset time);[lia|exact Resets|exact Steps|exact Lower|exact Upper|].
 intro site. cbn [store_part_expression nth reference_control_expr_2279 eval_hfexpr_validif_policy eval_href_validif_policy].
 rewrite SH;cbn. try rewrite V2274;try rewrite V2278.
 unfold eval_type_of_expr;cbn [type_of_expr' eval_type_of_ref];try rewrite V2274;try rewrite V2278.
 change (adapt_hvalue_as_type (Gval (Fuint 5) (store_immediate_low instruction)) (Gtyp (Fuint 5)) = Some (Gval (Fuint 5) (store_immediate_low instruction))). apply dut_decode_adapt. exact LowSize. }
 assert (V2280 : VM.find 2280 (history time) = Some (Gval (Fuint 5) (store_immediate_low instruction))).
 { eapply (store_part_value 25 inputs path history limit reset time);[lia|exact Resets|exact Steps|exact Lower|exact Upper|].
 intro site. cbn [store_part_expression nth reference_control_expr_2280 eval_hfexpr_validif_policy eval_href_validif_policy].
 rewrite SW;cbn. try rewrite V2271;try rewrite V2279.
 unfold eval_type_of_expr;cbn [type_of_expr' eval_type_of_ref];try rewrite V2271;try rewrite V2279.
 change (adapt_hvalue_as_type (Gval (Fuint 5) (store_immediate_low instruction)) (Gtyp (Fuint 5)) = Some (Gval (Fuint 5) (store_immediate_low instruction))). apply dut_decode_adapt. exact LowSize. }
 assert (V2281 : VM.find 2281 (history time) = Some (Gval (Fuint 5) (store_immediate_low instruction))).
 { eapply (store_part_value 26 inputs path history limit reset time);[lia|exact Resets|exact Steps|exact Lower|exact Upper|].
 intro site. cbn [store_part_expression nth reference_control_expr_2281 eval_hfexpr_validif_policy eval_href_validif_policy].
 rewrite Enabled;cbn. try rewrite V2280.
 unfold eval_type_of_expr;cbn [type_of_expr' eval_type_of_ref];try rewrite V2280.
 change (adapt_hvalue_as_type (Gval (Fuint 5) (store_immediate_low instruction)) (Gtyp (Fuint 5)) = Some (Gval (Fuint 5) (store_immediate_low instruction))). apply dut_decode_adapt. exact LowSize. }
 assert (V2282 : VM.find 2282 (history time) = Some (Gval (Fuint 5) (store_immediate_low instruction))).
 { eapply (store_part_value 27 inputs path history limit reset time);[lia|exact Resets|exact Steps|exact Lower|exact Upper|].
 intro site. cbn [store_part_expression nth reference_control_expr_2282 eval_hfexpr_validif_policy eval_href_validif_policy].
 exact V2281. }
 split;[exact V2268|exact V2282]. }
 destruct lane as [|lane].
 {
 cbn [Nat.eqb] in SW,SH,SB.
 assert (V2264 : VM.find 2264 (history time) = Some (Gval (Fuint 7) (store_immediate_high instruction))).
 { eapply (store_part_value 9 inputs path history limit reset time);[lia|exact Resets|exact Steps|exact Lower|exact Upper|].
 intro site. cbn [store_part_expression nth reference_control_expr_2264 eval_hfexpr_validif_policy eval_href_validif_policy].
 rewrite SB;cbn. try rewrite V2263.
 unfold eval_type_of_expr;cbn [type_of_expr' eval_type_of_ref];try rewrite V2263.
 change (adapt_hvalue_as_type (Gval (Fuint 7) (store_immediate_high instruction)) (Gtyp (Fuint 7)) = Some (Gval (Fuint 7) (store_immediate_high instruction))). apply dut_decode_adapt. exact HighSize. }
 assert (V2265 : VM.find 2265 (history time) = Some (Gval (Fuint 7) (store_immediate_high instruction))).
 { eapply (store_part_value 10 inputs path history limit reset time);[lia|exact Resets|exact Steps|exact Lower|exact Upper|].
 intro site. cbn [store_part_expression nth reference_control_expr_2265 eval_hfexpr_validif_policy eval_href_validif_policy].
 rewrite SH;cbn. try rewrite V2262;try rewrite V2264.
 unfold eval_type_of_expr;cbn [type_of_expr' eval_type_of_ref];try rewrite V2262;try rewrite V2264.
 change (adapt_hvalue_as_type (Gval (Fuint 7) (store_immediate_high instruction)) (Gtyp (Fuint 7)) = Some (Gval (Fuint 7) (store_immediate_high instruction))). apply dut_decode_adapt. exact HighSize. }
 assert (V2266 : VM.find 2266 (history time) = Some (Gval (Fuint 7) (store_immediate_high instruction))).
 { eapply (store_part_value 11 inputs path history limit reset time);[lia|exact Resets|exact Steps|exact Lower|exact Upper|].
 intro site. cbn [store_part_expression nth reference_control_expr_2266 eval_hfexpr_validif_policy eval_href_validif_policy].
 rewrite SW;cbn. try rewrite V2261;try rewrite V2265.
 unfold eval_type_of_expr;cbn [type_of_expr' eval_type_of_ref];try rewrite V2261;try rewrite V2265.
 change (adapt_hvalue_as_type (Gval (Fuint 7) (store_immediate_high instruction)) (Gtyp (Fuint 7)) = Some (Gval (Fuint 7) (store_immediate_high instruction))). apply dut_decode_adapt. exact HighSize. }
 assert (V2267 : VM.find 2267 (history time) = Some (Gval (Fuint 7) (store_immediate_high instruction))).
 { eapply (store_part_value 12 inputs path history limit reset time);[lia|exact Resets|exact Steps|exact Lower|exact Upper|].
 intro site. cbn [store_part_expression nth reference_control_expr_2267 eval_hfexpr_validif_policy eval_href_validif_policy].
 rewrite Enabled;cbn. try rewrite V2266.
 unfold eval_type_of_expr;cbn [type_of_expr' eval_type_of_ref];try rewrite V2266.
 change (adapt_hvalue_as_type (Gval (Fuint 7) (store_immediate_high instruction)) (Gtyp (Fuint 7)) = Some (Gval (Fuint 7) (store_immediate_high instruction))). apply dut_decode_adapt. exact HighSize. }
 assert (V2268 : VM.find 2268 (history time) = Some (Gval (Fuint 7) (store_immediate_high instruction))).
 { eapply (store_part_value 13 inputs path history limit reset time);[lia|exact Resets|exact Steps|exact Lower|exact Upper|].
 intro site. cbn [store_part_expression nth reference_control_expr_2268 eval_hfexpr_validif_policy eval_href_validif_policy].
 exact V2267. }
 assert (V2278 : VM.find 2278 (history time) = Some (Gval (Fuint 5) (store_immediate_low instruction))).
 { eapply (store_part_value 23 inputs path history limit reset time);[lia|exact Resets|exact Steps|exact Lower|exact Upper|].
 intro site. cbn [store_part_expression nth reference_control_expr_2278 eval_hfexpr_validif_policy eval_href_validif_policy].
 rewrite SB;cbn. try rewrite V2277.
 unfold eval_type_of_expr;cbn [type_of_expr' eval_type_of_ref];try rewrite V2277.
 change (adapt_hvalue_as_type (Gval (Fuint 5) (store_immediate_low instruction)) (Gtyp (Fuint 5)) = Some (Gval (Fuint 5) (store_immediate_low instruction))). apply dut_decode_adapt. exact LowSize. }
 assert (V2279 : VM.find 2279 (history time) = Some (Gval (Fuint 5) (store_immediate_low instruction))).
 { eapply (store_part_value 24 inputs path history limit reset time);[lia|exact Resets|exact Steps|exact Lower|exact Upper|].
 intro site. cbn [store_part_expression nth reference_control_expr_2279 eval_hfexpr_validif_policy eval_href_validif_policy].
 rewrite SH;cbn. try rewrite V2274;try rewrite V2278.
 unfold eval_type_of_expr;cbn [type_of_expr' eval_type_of_ref];try rewrite V2274;try rewrite V2278.
 change (adapt_hvalue_as_type (Gval (Fuint 5) (store_immediate_low instruction)) (Gtyp (Fuint 5)) = Some (Gval (Fuint 5) (store_immediate_low instruction))). apply dut_decode_adapt. exact LowSize. }
 assert (V2280 : VM.find 2280 (history time) = Some (Gval (Fuint 5) (store_immediate_low instruction))).
 { eapply (store_part_value 25 inputs path history limit reset time);[lia|exact Resets|exact Steps|exact Lower|exact Upper|].
 intro site. cbn [store_part_expression nth reference_control_expr_2280 eval_hfexpr_validif_policy eval_href_validif_policy].
 rewrite SW;cbn. try rewrite V2271;try rewrite V2279.
 unfold eval_type_of_expr;cbn [type_of_expr' eval_type_of_ref];try rewrite V2271;try rewrite V2279.
 change (adapt_hvalue_as_type (Gval (Fuint 5) (store_immediate_low instruction)) (Gtyp (Fuint 5)) = Some (Gval (Fuint 5) (store_immediate_low instruction))). apply dut_decode_adapt. exact LowSize. }
 assert (V2281 : VM.find 2281 (history time) = Some (Gval (Fuint 5) (store_immediate_low instruction))).
 { eapply (store_part_value 26 inputs path history limit reset time);[lia|exact Resets|exact Steps|exact Lower|exact Upper|].
 intro site. cbn [store_part_expression nth reference_control_expr_2281 eval_hfexpr_validif_policy eval_href_validif_policy].
 rewrite Enabled;cbn. try rewrite V2280.
 unfold eval_type_of_expr;cbn [type_of_expr' eval_type_of_ref];try rewrite V2280.
 change (adapt_hvalue_as_type (Gval (Fuint 5) (store_immediate_low instruction)) (Gtyp (Fuint 5)) = Some (Gval (Fuint 5) (store_immediate_low instruction))). apply dut_decode_adapt. exact LowSize. }
 assert (V2282 : VM.find 2282 (history time) = Some (Gval (Fuint 5) (store_immediate_low instruction))).
 { eapply (store_part_value 27 inputs path history limit reset time);[lia|exact Resets|exact Steps|exact Lower|exact Upper|].
 intro site. cbn [store_part_expression nth reference_control_expr_2282 eval_hfexpr_validif_policy eval_href_validif_policy].
 exact V2281. }
 split;[exact V2268|exact V2282]. }
 lia.
Qed.
Definition store_s_immediate instruction := sext_to 32 (store_immediate_low instruction ++ store_immediate_high instruction).
Lemma store_s_immediate_size instruction : size instruction = 32%nat -> size (store_s_immediate instruction) = 32%nat.
Proof.
 intro Size. unfold store_s_immediate,sext_to,sext.
 rewrite size_cat size_nseq size_cat. unfold store_immediate_low,store_immediate_high.
 rewrite !size_drop !size_take Size. reflexivity.
Qed.
Theorem reference_store_immediate_history inputs path history limit reset time instruction lane :
 (lane < 3)%coq_nat -> size instruction = 32%nat ->
 (forall t, (t <= limit)%coq_nat -> VM.find 1 (history t) = Some (Gval (Fuint 1) [::reset])) ->
 (forall t, (t < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history t) false (history t) flat_statements = Some (history (S t))) ->
 (forall t, (200 <= t)%coq_nat -> (t <= limit)%coq_nat -> VM.find 1884 (history t) = Some (Gval (Fuint 32) instruction)) ->
 (500 <= time)%coq_nat -> (time < limit)%coq_nat ->
 VM.find 1707 (history time) = Some (Gval (Fuint 1) [::true]) ->
 (forall n, (n < load_imm_mux_count true)%coq_nat -> VM.find (load_imm_mux_guard true n) (history time) = Some (Gval (Fuint 1) [::Nat.eqb n (Nat.sub 7 lane)])) ->
 VM.find 2552 (history time) = Some (Gval (Fuint 32) (store_s_immediate instruction)).
Proof.
 intros Lane Size Resets Steps Source Lower Upper Enabled Guards.
 pose proof (Guards 7%nat ltac:(cbn [load_imm_mux_count];lia)) as SW.
 pose proof (Guards 6%nat ltac:(cbn [load_imm_mux_count];lia)) as SH.
 pose proof (Guards 5%nat ltac:(cbn [load_imm_mux_count];lia)) as SB.
 cbn [load_imm_mux_guard nth] in SW,SH,SB.
 assert (Parts : VM.find 2268 (history time) = Some (Gval (Fuint 7) (store_immediate_high instruction)) /\
 VM.find 2282 (history time) = Some (Gval (Fuint 5) (store_immediate_low instruction))).
 { eapply (store_immediate_parts_history lane inputs path history limit reset time instruction);[exact Lane|exact Size|exact Resets|exact Steps|exact Lower|exact Upper|apply Source;lia|exact Enabled| | |];
 do 3 (destruct lane as [|lane];[assumption|]);lia. }
 destruct Parts as [High Low].
 assert (HighSize : size (store_immediate_high instruction) = 7%nat) by (unfold store_immediate_high;rewrite size_drop size_take Size;reflexivity).
 assert (LowSize : size (store_immediate_low instruction) = 5%nat) by (unfold store_immediate_low;rewrite size_drop size_take Size;reflexivity).
 pose proof (store_imm_sign_history lane inputs path history limit reset time _ _ Lane LowSize HighSize Resets Steps Lower Upper High Low) as Sign.
 assert (Selected : VM.find 2550 (history time) = Some (Gval (Fuint 32) (store_s_immediate instruction))).
 { change (VM.find (load_imm_mux_node true 10) (history time) = Some (Gval (Fuint (load_imm_mux_width true)) (store_s_immediate instruction))).
 eapply (load_imm_mux_suffix_history true inputs path history limit reset time (Nat.sub 7 lane) (store_s_immediate instruction));[cbn [load_imm_mux_count];lia|exact (store_s_immediate_size instruction Size)|exact Resets|exact Steps| |exact Lower|exact Upper|exact Guards|exact Sign|lia|cbn [load_imm_mux_count];lia].
 intros t L U. exists (Gval (Fuint 32) instruction);split;[apply Source;assumption|reflexivity]. }
 assert (EnabledValue : VM.find 2551 (history time) = Some (Gval (Fuint 32) (store_s_immediate instruction))).
 { eapply (load_imm_aux_value 27 inputs path history limit reset time);[lia|exact Resets|exact Steps|exact Lower|exact Upper|].
 intro site. cbn [load_imm_aux_expression load_imm_aux_expressions nth reference_control_expr_2551 eval_hfexpr_validif_policy eval_href_validif_policy].
 rewrite Enabled;cbn;rewrite Selected. change (adapt_hvalue_as_type (Gval (Fuint 32) (store_s_immediate instruction)) (Gtyp (Fuint 32)) = Some (Gval (Fuint 32) (store_s_immediate instruction))). apply dut_decode_adapt;exact (store_s_immediate_size instruction Size). }
 eapply (load_imm_aux_value 28 inputs path history limit reset time);[lia|exact Resets|exact Steps|exact Lower|exact Upper|].
 intro site. exact EnabledValue.
Qed.
