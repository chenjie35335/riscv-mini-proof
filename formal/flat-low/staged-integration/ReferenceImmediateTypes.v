Require Import X0ConcretePositionCertificate X0ConcreteSafetyCertificate CoreSocModel ComparisonNodes ReferenceControlExpressions ReferenceControlNodeCongruence0 ReferenceControlNodeCongruence1 ReferenceControlNodeCongruence2 ReferenceControlNodeCertificates0 ReferenceControlNodeCertificates1 ReferenceControlNodeCertificates2 ReferenceRedirectSpine FormalSuccessfulNodeEvaluation SelectedNodeSafety FormalTypedNodeEquation ScalarSinkTypes DUTRedirectDecode.
From Coq Require Import NArith ZArith List Lia.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From nbits Require Import NBits.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Firrtl_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Local Opaque flat_statements flat_memories generated_modules generated_top.
Inductive immediate_leaf (old:VM.t hvalue) : hfexpr VarOrder.T -> nat -> Prop :=
| immediate_const width bits : size bits = width -> immediate_leaf old (@Econst VarOrder.T (Fuint width) bits) width
| immediate_ref node width value : VM.find node old = Some value -> type_of_val value = Gtyp (Fuint width) -> immediate_leaf old (@Eref VarOrder.T (@Eid VarOrder.T node)) width.
Lemma immediate_leaf_value old expression width : immediate_leaf old expression width ->
 exists value, type_of_val value = Gtyp (Fuint width) /\ eval_type_of_expr expression old = Some (Gtyp (Fuint width)) /\
 forall invalid site, eval_hfexpr_validif_policy invalid site flat_memories expression old old = Some value.
Proof.
 intro Leaf. destruct Leaf as [width bits Size|node width value Lookup Typed].
 - exists (Gval (Fuint width) bits). split;[reflexivity|]. split.
   + unfold eval_type_of_expr;cbn [type_of_expr'];rewrite Size ltnn;reflexivity.
   + intros invalid site;cbn [eval_hfexpr_validif_policy];rewrite Size ltnn.
     unfold zext_to;rewrite Size subnn;unfold zext;rewrite zeros0 cats0;reflexivity.
 - exists value. split;[exact Typed|]. split.
   + unfold eval_type_of_expr;cbn [type_of_expr' eval_type_of_ref];rewrite Lookup;cbn [option_map];rewrite Typed;reflexivity.
   + intros invalid site;exact Lookup.
Qed.
Lemma immediate_extract_type input width hi lo result :
 type_of_val input = Gtyp (Fuint width) -> eval_unop (Uextr hi lo) input = Some result ->
 type_of_val result = Gtyp (Fuint (hi.+1-lo)).
Proof.
 destruct input as [ground bits|element values|fields|typ|typ|typ];cbn;intros Typed Eval;try discriminate Typed;
 inversion Typed;subst;cbn [eval_unop] in Eval;
 repeat match type of Eval with context[if ?b then _ else _] => destruct b end;
 try discriminate Eval;inversion Eval;reflexivity.
Qed.
Lemma immediate_cat_no_absorbing left right : absorbing_bit Bcat left right = None.
Proof. unfold absorbing_bit. destruct ((type_of_val left == Gtyp (Fuint 1)) && (type_of_val right == Gtyp (Fuint 1)));reflexivity. Qed.
Lemma immediate_cat_type left right lw rw result :
 type_of_val left = Gtyp (Fuint lw) -> type_of_val right = Gtyp (Fuint rw) ->
 eval_binop Bcat left right = Some result -> type_of_val result = Gtyp (Fuint (lw+rw)).
Proof.
 destruct left as [lg lb|le la|lf|lt|lt|lt];cbn;intro LT;try discriminate LT;inversion LT;subst;
 destruct right as [rg rb|re ra|rf|rt|rt|rt];cbn;intro RT;try discriminate RT;inversion RT;subst;
 unfold eval_binop;rewrite immediate_cat_no_absorbing;cbn [eval_binop_basic refine_boolean_result];intro Eval;inversion Eval;reflexivity.
Qed.
Lemma immediate_mux_type invalid site old condition yes no yw nw result :
 immediate_leaf old yes yw -> immediate_leaf old no nw ->
 eval_hfexpr_validif_policy invalid site flat_memories (@Emux VarOrder.T condition yes no) old old = Some result ->
 type_of_val result = Gtyp (Fuint (maxn yw nw)).
Proof.
 intros Yes No Eval. destruct (immediate_leaf_value old yes yw Yes) as [yv [YT [YE YV]]].
 destruct (immediate_leaf_value old no nw No) as [nv [NT [NE NV]]].
 cbn [eval_hfexpr_validif_policy] in Eval.
 destruct (eval_hfexpr_validif_policy invalid _ flat_memories condition old old) as [value|] eqn:C;[|discriminate Eval].
 destruct value as [ground bits|element values|fields|typ|typ|typ];try discriminate Eval.
 - destruct ground;try discriminate Eval. destruct (is_zero bits);rewrite ?YV ?NV ?YE ?NE in Eval;
   unfold extend_hvalue_as_type in Eval;rewrite ?YT ?NT in Eval;cbn [ftype_mux fgtyp_mux] in Eval;
   try rewrite (maxnC nw yw) in Eval;eapply adapted_uint_result_type;exact Eval.
 - destruct typ as [ground|element count|fields];try discriminate Eval;destruct ground;try discriminate Eval;
   rewrite YE NE in Eval;cbn [ftype_mux fgtyp_mux option_map] in Eval;inversion Eval;reflexivity.
 - destruct typ as [ground|element count|fields];try discriminate Eval;destruct ground;try discriminate Eval;
   rewrite YE NE in Eval;cbn [ftype_mux fgtyp_mux option_map] in Eval;inversion Eval;reflexivity.
 - destruct typ as [ground|element count|fields];try discriminate Eval;destruct ground;try discriminate Eval;
   rewrite YE NE in Eval;cbn [ftype_mux fgtyp_mux option_map] in Eval;inversion Eval;reflexivity.
Qed.
Definition immediate_leaf_check (width_of:VarOrder.T -> nat) (expression:hfexpr VarOrder.T) : option (nat * seq VarOrder.T) :=
 match expression with
 | Econst (Fuint width) bits => if size bits == width then Some (width,[::]) else None
 | Eref (Eid node) => Some (width_of node,[::node])
 | _ => None end.
Definition immediate_expression_check (width_of:VarOrder.T -> nat) (expression:hfexpr VarOrder.T) : option (nat * seq VarOrder.T) :=
 match expression with
 | Eprim_unop (Uextr hi lo) arg =>
   match immediate_leaf_check width_of arg with Some (_,refs) => Some ((hi.+1-lo)%nat,refs) | _ => None end
 | Eprim_binop Bcat lhs rhs =>
   match immediate_leaf_check width_of lhs,immediate_leaf_check width_of rhs with
   | Some (lw,lr),Some (rw,rr) => Some ((lw+rw)%nat,lr++rr) | _,_ => None end
 | Emux condition yes no =>
   match immediate_leaf_check width_of yes,immediate_leaf_check width_of no with
   | Some (yw,yr),Some (nw,nr) => Some (maxn yw nw,yr++nr) | _,_ => None end
 | _ => immediate_leaf_check width_of expression end.
Lemma immediate_leaf_check_sound width_of expression width refs old :
 immediate_leaf_check width_of expression = Some (width,refs) ->
 (forall node, List.In node refs -> exists value, VM.find node old = Some value /\ type_of_val value = Gtyp (Fuint (width_of node))) ->
 immediate_leaf old expression width.
Proof.
 destruct expression as [ground bits|cast arg|op arg|op left right|condition yes no|condition arg|reference];cbn [immediate_leaf_check];try discriminate.
 - destruct ground;try discriminate. destruct (size bits == n) eqn:Size;try discriminate.
   intros Check Sources. inversion Check;subst. apply immediate_const. exact (elimT eqP Size).
 - destruct reference;try discriminate. intros Check Sources. inversion Check;subst.
   destruct (Sources _ (or_introl (Logic.eq_refl _))) as [value [Lookup Typed]]. eapply immediate_ref;[exact Lookup|exact Typed].
Qed.
Lemma immediate_expression_check_sound width_of expression width refs old invalid site result :
 immediate_expression_check width_of expression = Some (width,refs) ->
 (forall node, List.In node refs -> exists value, VM.find node old = Some value /\ type_of_val value = Gtyp (Fuint (width_of node))) ->
 eval_hfexpr_validif_policy invalid site flat_memories expression old old = Some result -> type_of_val result = Gtyp (Fuint width).
Proof.
 destruct expression as [ground bits|cast arg|op arg|op left right|condition yes no|condition arg|reference];
 try (intros Check Sources Eval;destruct (immediate_leaf_value old _ _ (immediate_leaf_check_sound _ _ _ _ _ Check Sources)) as [value [Typed [_ Value]]];rewrite Value in Eval;inversion Eval;subst;exact Typed).
 - destruct op;try discriminate. cbn [immediate_expression_check].
   destruct (immediate_leaf_check width_of arg) as [[aw ar]|] eqn:A;try discriminate.
   intros Check Sources Eval. inversion Check;subst.
   destruct (immediate_leaf_value old arg aw (immediate_leaf_check_sound _ _ _ _ _ A Sources)) as [value [Typed [_ Value]]].
   cbn [eval_hfexpr_validif_policy] in Eval. rewrite Value in Eval. eapply immediate_extract_type;[exact Typed|exact Eval].
 - destruct op;try discriminate. cbn [immediate_expression_check].
   destruct (immediate_leaf_check width_of left) as [[lw lr]|] eqn:L;try discriminate.
   destruct (immediate_leaf_check width_of right) as [[rw rr]|] eqn:R;try discriminate.
   intros Check Sources Eval. inversion Check;subst.
   assert (LS : forall node, List.In node lr -> exists value, VM.find node old = Some value /\ type_of_val value = Gtyp (Fuint (width_of node))).
   { intros node Member;apply Sources;apply List.in_or_app;left;exact Member. }
   assert (RS : forall node, List.In node rr -> exists value, VM.find node old = Some value /\ type_of_val value = Gtyp (Fuint (width_of node))).
   { intros node Member;apply Sources;apply List.in_or_app;right;exact Member. }
   destruct (immediate_leaf_value old left lw (immediate_leaf_check_sound _ _ _ _ _ L LS)) as [lv [LT [_ LV]]].
   destruct (immediate_leaf_value old right rw (immediate_leaf_check_sound _ _ _ _ _ R RS)) as [rv [RT [_ RV]]].
   cbn [eval_hfexpr_validif_policy] in Eval. rewrite LV RV in Eval. eapply immediate_cat_type;[exact LT|exact RT|exact Eval].
 - cbn [immediate_expression_check].
   destruct (immediate_leaf_check width_of yes) as [[yw yr]|] eqn:Y;try discriminate.
   destruct (immediate_leaf_check width_of no) as [[nw nr]|] eqn:N;try discriminate.
   intros Check Sources Eval. inversion Check;subst. eapply immediate_mux_type;[| |exact Eval].
   + apply (immediate_leaf_check_sound _ _ _ _ _ Y). intros node Member;apply Sources;apply List.in_or_app;left;exact Member.
   + apply (immediate_leaf_check_sound _ _ _ _ _ N). intros node Member;apply Sources;apply List.in_or_app;right;exact Member.
Qed.
(* Generated immediate type DAG. *)
Definition reference_immediate_ids : seq VarOrder.T := [::1942;1943;1947;1948;1952;1953;1975;1976;1977;1981;1982;1983;1987;1988;1989;1993;1994;1995;1999;2000;2001;2005;2006;2007;2211;2212;2213;2214;2215;2216;2217;2218;2219;2220;2221;2222;2223;2224;2225;2226;2227;2228;2229;2230;2231;2232;2233;2234;2235;2236;2237;2238;2239;2240;2241;2242;2243;2244;2245;2246;2247;2248;2251;2252;2255;2256;2259;2260;2261;2262;2263;2264;2265;2266;2267;2268;2269;2270;2271;2272;2273;2274;2275;2276;2277;2278;2279;2280;2281;2282;2283;2286;2287;2288;2291;2292;2293;2296;2297;2300;2301;2304;2305;2308;2309;2312;2313;2316;2317;2318;2319;2320;2321;2322;2323;2324;2325;2326;2327;2328;2329;2330;2331;2332;2333;2334;2335;2336;2337;2338;2339;2340;2341;2342;2343;2344;2345;2346;2347;2348;2349;2350;2351;2352;2353;2354;2355;2358;2359;2360;2361;2362;2363;2364;2365;2366;2367;2368;2369;2370;2371;2372;2373;2374;2375;2376;2377;2378;2379;2380;2381;2382;2383;2384;2385;2386;2387;2388;2389;2390;2391;2392;2393;2394;2395;2396;2397;2398;2399;2400;2401;2404;2405;2406;2407;2408;2409;2412;2413;2414;2415;2416;2417;2420;2421;2422;2423;2424;2425;2428;2429;2430;2431;2432;2433;2436;2437;2438;2439;2440;2441;2444;2445;2448;2449;2450;2451;2452;2453;2454;2455;2456;2457;2458;2459;2460;2461;2462;2463;2464;2465;2466;2469;2470;2473;2476;2477;2478;2479;2480;2481;2482;2483;2484;2487;2488;2491;2492;2495;2496;2499;2500;2503;2504;2507;2508;2511;2512;2515;2516;2519;2520;2521;2522;2523;2524;2525;2526;2527;2528;2529;2530;2531;2532;2533;2534;2535;2536;2537;2538;2539;2540;2541;2542;2543;2544;2545;2546;2547;2548;2549;2550;2551;2552].
Definition reference_immediate_widths : seq nat := [::25%nat;20%nat;25%nat;20%nat;25%nat;20%nat;31%nat;25%nat;20%nat;31%nat;25%nat;20%nat;31%nat;25%nat;20%nat;31%nat;25%nat;20%nat;31%nat;25%nat;20%nat;31%nat;25%nat;20%nat;12%nat;12%nat;12%nat;12%nat;12%nat;12%nat;12%nat;12%nat;12%nat;12%nat;12%nat;12%nat;12%nat;12%nat;12%nat;12%nat;12%nat;12%nat;12%nat;12%nat;12%nat;12%nat;12%nat;12%nat;12%nat;12%nat;12%nat;12%nat;12%nat;12%nat;12%nat;12%nat;12%nat;12%nat;12%nat;12%nat;12%nat;12%nat;20%nat;32%nat;20%nat;32%nat;20%nat;32%nat;7%nat;7%nat;7%nat;7%nat;7%nat;7%nat;7%nat;7%nat;15%nat;12%nat;5%nat;15%nat;12%nat;5%nat;15%nat;12%nat;5%nat;5%nat;5%nat;5%nat;5%nat;5%nat;12%nat;20%nat;32%nat;12%nat;20%nat;32%nat;12%nat;20%nat;32%nat;20%nat;32%nat;20%nat;32%nat;20%nat;32%nat;20%nat;32%nat;20%nat;32%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;15%nat;12%nat;8%nat;1%nat;15%nat;12%nat;8%nat;1%nat;15%nat;12%nat;8%nat;1%nat;15%nat;12%nat;8%nat;1%nat;15%nat;12%nat;8%nat;1%nat;15%nat;12%nat;8%nat;1%nat;31%nat;21%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;2%nat;6%nat;6%nat;6%nat;6%nat;6%nat;6%nat;6%nat;6%nat;6%nat;6%nat;6%nat;6%nat;6%nat;6%nat;8%nat;4%nat;4%nat;4%nat;4%nat;4%nat;4%nat;4%nat;4%nat;4%nat;4%nat;4%nat;4%nat;4%nat;4%nat;5%nat;13%nat;19%nat;32%nat;2%nat;8%nat;5%nat;13%nat;19%nat;32%nat;2%nat;8%nat;5%nat;13%nat;19%nat;32%nat;2%nat;8%nat;5%nat;13%nat;19%nat;32%nat;2%nat;8%nat;5%nat;13%nat;19%nat;32%nat;2%nat;8%nat;5%nat;13%nat;19%nat;32%nat;20%nat;32%nat;1%nat;1%nat;1%nat;1%nat;20%nat;8%nat;8%nat;8%nat;8%nat;9%nat;10%nat;10%nat;10%nat;10%nat;10%nat;11%nat;21%nat;11%nat;32%nat;20%nat;20%nat;20%nat;20%nat;20%nat;20%nat;32%nat;32%nat;32%nat;32%nat;20%nat;32%nat;20%nat;32%nat;20%nat;32%nat;20%nat;32%nat;20%nat;32%nat;20%nat;32%nat;20%nat;32%nat;20%nat;32%nat;20%nat;32%nat;32%nat;32%nat;32%nat;32%nat;32%nat;32%nat;32%nat;32%nat;32%nat;32%nat;32%nat;32%nat;32%nat;32%nat;32%nat;32%nat;32%nat;32%nat;32%nat;32%nat;32%nat;32%nat;32%nat;32%nat;32%nat;32%nat;32%nat;32%nat;32%nat;32%nat;32%nat;32%nat].
Definition reference_immediate_ranks : seq nat := [::1%nat;2%nat;1%nat;2%nat;1%nat;2%nat;1%nat;2%nat;3%nat;1%nat;2%nat;3%nat;1%nat;2%nat;3%nat;1%nat;2%nat;3%nat;1%nat;2%nat;3%nat;1%nat;2%nat;3%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;2%nat;3%nat;4%nat;5%nat;6%nat;7%nat;8%nat;9%nat;10%nat;11%nat;12%nat;13%nat;14%nat;15%nat;16%nat;17%nat;18%nat;19%nat;20%nat;21%nat;1%nat;22%nat;1%nat;22%nat;1%nat;22%nat;1%nat;1%nat;1%nat;2%nat;3%nat;4%nat;5%nat;6%nat;3%nat;4%nat;5%nat;3%nat;4%nat;5%nat;3%nat;4%nat;5%nat;6%nat;7%nat;8%nat;9%nat;10%nat;11%nat;1%nat;12%nat;11%nat;1%nat;12%nat;11%nat;1%nat;12%nat;1%nat;22%nat;1%nat;22%nat;1%nat;22%nat;1%nat;22%nat;1%nat;22%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;2%nat;3%nat;4%nat;5%nat;6%nat;7%nat;8%nat;9%nat;4%nat;5%nat;6%nat;7%nat;4%nat;5%nat;6%nat;7%nat;4%nat;5%nat;6%nat;7%nat;4%nat;5%nat;6%nat;7%nat;4%nat;5%nat;6%nat;7%nat;4%nat;5%nat;6%nat;7%nat;1%nat;2%nat;3%nat;4%nat;8%nat;9%nat;10%nat;11%nat;12%nat;13%nat;14%nat;15%nat;16%nat;2%nat;2%nat;2%nat;2%nat;2%nat;2%nat;3%nat;4%nat;5%nat;6%nat;7%nat;8%nat;9%nat;10%nat;17%nat;6%nat;6%nat;6%nat;6%nat;6%nat;6%nat;7%nat;8%nat;9%nat;10%nat;11%nat;12%nat;13%nat;14%nat;15%nat;18%nat;1%nat;19%nat;16%nat;17%nat;15%nat;18%nat;1%nat;19%nat;16%nat;17%nat;15%nat;18%nat;1%nat;19%nat;16%nat;17%nat;15%nat;18%nat;1%nat;19%nat;16%nat;17%nat;15%nat;18%nat;1%nat;19%nat;16%nat;17%nat;15%nat;18%nat;1%nat;19%nat;1%nat;22%nat;1%nat;2%nat;3%nat;4%nat;3%nat;4%nat;5%nat;6%nat;7%nat;8%nat;16%nat;2%nat;3%nat;4%nat;5%nat;6%nat;17%nat;1%nat;18%nat;1%nat;1%nat;2%nat;3%nat;4%nat;5%nat;6%nat;7%nat;6%nat;7%nat;1%nat;22%nat;1%nat;22%nat;1%nat;22%nat;1%nat;22%nat;1%nat;22%nat;1%nat;22%nat;1%nat;22%nat;1%nat;22%nat;1%nat;22%nat;23%nat;24%nat;25%nat;26%nat;27%nat;28%nat;29%nat;30%nat;31%nat;32%nat;33%nat;34%nat;35%nat;36%nat;37%nat;38%nat;39%nat;40%nat;41%nat;42%nat;43%nat;44%nat;45%nat;46%nat;47%nat;48%nat;49%nat;50%nat;51%nat;52%nat;53%nat;54%nat].
Definition reference_immediate_groups : seq nat := [::0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;2%nat;2%nat;2%nat;2%nat;2%nat;2%nat;2%nat;2%nat;2%nat;2%nat;2%nat;2%nat;2%nat;2%nat;2%nat;2%nat;2%nat;2%nat;2%nat;2%nat;2%nat;2%nat;2%nat;2%nat;2%nat;2%nat;2%nat;2%nat;2%nat;2%nat;2%nat;2%nat;2%nat;2%nat;2%nat;2%nat;2%nat;2%nat;2%nat;2%nat;2%nat;2%nat;2%nat;2%nat;2%nat;2%nat;2%nat;2%nat;2%nat;2%nat;2%nat;2%nat].
Definition reference_immediate_expressions : seq (hfexpr VarOrder.T) := [::reference_control_expr_1942;reference_control_expr_1943;reference_control_expr_1947;reference_control_expr_1948;reference_control_expr_1952;reference_control_expr_1953;reference_control_expr_1975;reference_control_expr_1976;reference_control_expr_1977;reference_control_expr_1981;reference_control_expr_1982;reference_control_expr_1983;reference_control_expr_1987;reference_control_expr_1988;reference_control_expr_1989;reference_control_expr_1993;reference_control_expr_1994;reference_control_expr_1995;reference_control_expr_1999;reference_control_expr_2000;reference_control_expr_2001;reference_control_expr_2005;reference_control_expr_2006;reference_control_expr_2007;reference_control_expr_2211;reference_control_expr_2212;reference_control_expr_2213;reference_control_expr_2214;reference_control_expr_2215;reference_control_expr_2216;reference_control_expr_2217;reference_control_expr_2218;reference_control_expr_2219;reference_control_expr_2220;reference_control_expr_2221;reference_control_expr_2222;reference_control_expr_2223;reference_control_expr_2224;reference_control_expr_2225;reference_control_expr_2226;reference_control_expr_2227;reference_control_expr_2228;reference_control_expr_2229;reference_control_expr_2230;reference_control_expr_2231;reference_control_expr_2232;reference_control_expr_2233;reference_control_expr_2234;reference_control_expr_2235;reference_control_expr_2236;reference_control_expr_2237;reference_control_expr_2238;reference_control_expr_2239;reference_control_expr_2240;reference_control_expr_2241;reference_control_expr_2242;reference_control_expr_2243;reference_control_expr_2244;reference_control_expr_2245;reference_control_expr_2246;reference_control_expr_2247;reference_control_expr_2248;reference_control_expr_2251;reference_control_expr_2252;reference_control_expr_2255;reference_control_expr_2256;reference_control_expr_2259;reference_control_expr_2260;reference_control_expr_2261;reference_control_expr_2262;reference_control_expr_2263;reference_control_expr_2264;reference_control_expr_2265;reference_control_expr_2266;reference_control_expr_2267;reference_control_expr_2268;reference_control_expr_2269;reference_control_expr_2270;reference_control_expr_2271;reference_control_expr_2272;reference_control_expr_2273;reference_control_expr_2274;reference_control_expr_2275;reference_control_expr_2276;reference_control_expr_2277;reference_control_expr_2278;reference_control_expr_2279;reference_control_expr_2280;reference_control_expr_2281;reference_control_expr_2282;reference_control_expr_2283;reference_control_expr_2286;reference_control_expr_2287;reference_control_expr_2288;reference_control_expr_2291;reference_control_expr_2292;reference_control_expr_2293;reference_control_expr_2296;reference_control_expr_2297;reference_control_expr_2300;reference_control_expr_2301;reference_control_expr_2304;reference_control_expr_2305;reference_control_expr_2308;reference_control_expr_2309;reference_control_expr_2312;reference_control_expr_2313;reference_control_expr_2316;reference_control_expr_2317;reference_control_expr_2318;reference_control_expr_2319;reference_control_expr_2320;reference_control_expr_2321;reference_control_expr_2322;reference_control_expr_2323;reference_control_expr_2324;reference_control_expr_2325;reference_control_expr_2326;reference_control_expr_2327;reference_control_expr_2328;reference_control_expr_2329;reference_control_expr_2330;reference_control_expr_2331;reference_control_expr_2332;reference_control_expr_2333;reference_control_expr_2334;reference_control_expr_2335;reference_control_expr_2336;reference_control_expr_2337;reference_control_expr_2338;reference_control_expr_2339;reference_control_expr_2340;reference_control_expr_2341;reference_control_expr_2342;reference_control_expr_2343;reference_control_expr_2344;reference_control_expr_2345;reference_control_expr_2346;reference_control_expr_2347;reference_control_expr_2348;reference_control_expr_2349;reference_control_expr_2350;reference_control_expr_2351;reference_control_expr_2352;reference_control_expr_2353;reference_control_expr_2354;reference_control_expr_2355;reference_control_expr_2358;reference_control_expr_2359;reference_control_expr_2360;reference_control_expr_2361;reference_control_expr_2362;reference_control_expr_2363;reference_control_expr_2364;reference_control_expr_2365;reference_control_expr_2366;reference_control_expr_2367;reference_control_expr_2368;reference_control_expr_2369;reference_control_expr_2370;reference_control_expr_2371;reference_control_expr_2372;reference_control_expr_2373;reference_control_expr_2374;reference_control_expr_2375;reference_control_expr_2376;reference_control_expr_2377;reference_control_expr_2378;reference_control_expr_2379;reference_control_expr_2380;reference_control_expr_2381;reference_control_expr_2382;reference_control_expr_2383;reference_control_expr_2384;reference_control_expr_2385;reference_control_expr_2386;reference_control_expr_2387;reference_control_expr_2388;reference_control_expr_2389;reference_control_expr_2390;reference_control_expr_2391;reference_control_expr_2392;reference_control_expr_2393;reference_control_expr_2394;reference_control_expr_2395;reference_control_expr_2396;reference_control_expr_2397;reference_control_expr_2398;reference_control_expr_2399;reference_control_expr_2400;reference_control_expr_2401;reference_control_expr_2404;reference_control_expr_2405;reference_control_expr_2406;reference_control_expr_2407;reference_control_expr_2408;reference_control_expr_2409;reference_control_expr_2412;reference_control_expr_2413;reference_control_expr_2414;reference_control_expr_2415;reference_control_expr_2416;reference_control_expr_2417;reference_control_expr_2420;reference_control_expr_2421;reference_control_expr_2422;reference_control_expr_2423;reference_control_expr_2424;reference_control_expr_2425;reference_control_expr_2428;reference_control_expr_2429;reference_control_expr_2430;reference_control_expr_2431;reference_control_expr_2432;reference_control_expr_2433;reference_control_expr_2436;reference_control_expr_2437;reference_control_expr_2438;reference_control_expr_2439;reference_control_expr_2440;reference_control_expr_2441;reference_control_expr_2444;reference_control_expr_2445;reference_control_expr_2448;reference_control_expr_2449;reference_control_expr_2450;reference_control_expr_2451;reference_control_expr_2452;reference_control_expr_2453;reference_control_expr_2454;reference_control_expr_2455;reference_control_expr_2456;reference_control_expr_2457;reference_control_expr_2458;reference_control_expr_2459;reference_control_expr_2460;reference_control_expr_2461;reference_control_expr_2462;reference_control_expr_2463;reference_control_expr_2464;reference_control_expr_2465;reference_control_expr_2466;reference_control_expr_2469;reference_control_expr_2470;reference_control_expr_2473;reference_control_expr_2476;reference_control_expr_2477;reference_control_expr_2478;reference_control_expr_2479;reference_control_expr_2480;reference_control_expr_2481;reference_control_expr_2482;reference_control_expr_2483;reference_control_expr_2484;reference_control_expr_2487;reference_control_expr_2488;reference_control_expr_2491;reference_control_expr_2492;reference_control_expr_2495;reference_control_expr_2496;reference_control_expr_2499;reference_control_expr_2500;reference_control_expr_2503;reference_control_expr_2504;reference_control_expr_2507;reference_control_expr_2508;reference_control_expr_2511;reference_control_expr_2512;reference_control_expr_2515;reference_control_expr_2516;reference_control_expr_2519;reference_control_expr_2520;reference_control_expr_2521;reference_control_expr_2522;reference_control_expr_2523;reference_control_expr_2524;reference_control_expr_2525;reference_control_expr_2526;reference_control_expr_2527;reference_control_expr_2528;reference_control_expr_2529;reference_control_expr_2530;reference_control_expr_2531;reference_control_expr_2532;reference_control_expr_2533;reference_control_expr_2534;reference_control_expr_2535;reference_control_expr_2536;reference_control_expr_2537;reference_control_expr_2538;reference_control_expr_2539;reference_control_expr_2540;reference_control_expr_2541;reference_control_expr_2542;reference_control_expr_2543;reference_control_expr_2544;reference_control_expr_2545;reference_control_expr_2546;reference_control_expr_2547;reference_control_expr_2548;reference_control_expr_2549;reference_control_expr_2550;reference_control_expr_2551;reference_control_expr_2552].
Definition reference_immediate_dependencies : seq (seq VarOrder.T) := [::[::1884];[::1942];[::1884];[::1947];[::1884];[::1952];[::1884];[::1975];[::1976];[::1884];[::1981];[::1982];[::1884];[::1987];[::1988];[::1884];[::1993];[::1994];[::1884];[::1999];[::2000];[::1884];[::2005];[::2006];[::1884];[::1884];[::1884];[::1884];[::1884];[::1884];[::1884];[::1884];[::1884];[::1884];[::1884];[::1884];[::1884];[::1884];[::1884];[::1884];[::1884];[::1884];[::2228];[::2227;2229];[::2226;2230];[::2225;2231];[::2224;2232];[::2223;2233];[::2222;2234];[::2221;2235];[::2220;2236];[::2219;2237];[::2218;2238];[::2217;2239];[::2216;2240];[::2215;2241];[::2214;2242];[::2213;2243];[::2212;2244];[::2211;2245];[::2246];[::2247];[::];[::2251;2248];[::];[::2255;2248];[::];[::2259;2248];[::1884];[::1884];[::1884];[::2263];[::2262;2264];[::2261;2265];[::2266];[::2267];[::1943];[::2269];[::2270];[::1948];[::2272];[::2273];[::1953];[::2275];[::2276];[::2277];[::2274;2278];[::2271;2279];[::2280];[::2281];[::2268;2282];[::];[::2286;2283];[::2268;2282];[::];[::2291;2288];[::2268;2282];[::];[::2296;2293];[::];[::2300;2248];[::];[::2304;2248];[::];[::2308;2248];[::];[::2312;2248];[::];[::2316;2248];[::1884];[::1884];[::1884];[::1884];[::1884];[::1884];[::2323];[::2322;2324];[::2321;2325];[::2320;2326];[::2319;2327];[::2318;2328];[::2329];[::2330];[::1977];[::2332];[::2333];[::2334];[::1983];[::2336];[::2337];[::2338];[::1989];[::2340];[::2341];[::2342];[::1995];[::2344];[::2345];[::2346];[::2001];[::2348];[::2349];[::2350];[::2007];[::2352];[::2353];[::2354];[::1884];[::2358];[::2359];[::2360];[::2355;2361];[::2351;2362];[::2347;2363];[::2343;2364];[::2339;2365];[::2335;2366];[::2367];[::2368];[::2331;2369];[::1975];[::1981];[::1987];[::1993];[::1999];[::2005];[::2376];[::2375;2377];[::2374;2378];[::2373;2379];[::2372;2380];[::2371;2381];[::2382];[::2383];[::2370;2384];[::2333];[::2337];[::2341];[::2345];[::2349];[::2353];[::2391];[::2390;2392];[::2389;2393];[::2388;2394];[::2387;2395];[::2386;2396];[::2397];[::2398];[::2399];[::2385;2400];[::];[::2404;2401];[::2331;2369];[::2406;2384];[::2399];[::2407;2408];[::];[::2412;2409];[::2331;2369];[::2414;2384];[::2399];[::2415;2416];[::];[::2420;2417];[::2331;2369];[::2422;2384];[::2399];[::2423;2424];[::];[::2428;2425];[::2331;2369];[::2430;2384];[::2399];[::2431;2432];[::];[::2436;2433];[::2331;2369];[::2438;2384];[::2399];[::2439;2440];[::];[::2444;2441];[::];[::2448;2248];[::1884];[::2450];[::2451];[::2452];[::2359];[::2454];[::2455];[::2456];[::2457];[::2453;2458];[::2459;2369];[::2358];[::2461];[::2462];[::2463];[::2464];[::2460;2465];[::];[::2469;2466];[::1884];[::1884];[::2476];[::2473;2477];[::2478];[::2479];[::2480];[::2481];[::2480];[::2483];[::];[::2487;2248];[::];[::2491;2248];[::];[::2495;2248];[::];[::2499;2248];[::];[::2503;2248];[::];[::2507;2248];[::];[::2511;2248];[::];[::2515;2248];[::];[::2519;2248];[::2520];[::2516;2521];[::2512;2522];[::2508;2523];[::2504;2524];[::2500;2525];[::2496;2526];[::2492;2527];[::2488;2528];[::2484;2529];[::2482;2530];[::2470;2531];[::2449;2532];[::2445;2533];[::2437;2534];[::2429;2535];[::2421;2536];[::2413;2537];[::2405;2538];[::2317;2539];[::2313;2540];[::2309;2541];[::2305;2542];[::2301;2543];[::2297;2544];[::2292;2545];[::2287;2546];[::2260;2547];[::2256;2548];[::2252;2549];[::2550];[::2551]].
Definition reference_immediate_node i := nth 0 reference_immediate_ids i.
Definition reference_immediate_width i := nth 0%nat reference_immediate_widths i.
Definition reference_immediate_rank i := nth 0%nat reference_immediate_ranks i.
Definition reference_immediate_expression i := nth (@Econst VarOrder.T (Fuint 1) [::false]) reference_immediate_expressions i.
Definition reference_immediate_refs i := nth [::] reference_immediate_dependencies i.
Definition reference_immediate_width_of node := if node == 1884 then 32%nat else reference_immediate_width (index node reference_immediate_ids).
Definition reference_immediate_nodes i := match nth 2%nat reference_immediate_groups i with O => reference_control_0_nodes | S O => reference_control_1_nodes | _ => reference_control_2_nodes end.
Definition reference_immediate_offsets i := match nth 2%nat reference_immediate_groups i with O => reference_control_0_offsets | S O => reference_control_1_offsets | _ => reference_control_2_offsets end.
Lemma reference_immediate_plan i : (i < 304)%coq_nat ->
 immediate_expression_check reference_immediate_width_of (reference_immediate_expression i) = Some (reference_immediate_width i,reference_immediate_refs i) /\ (0 < reference_immediate_rank i)%coq_nat.
Proof. intro Bound. do 304 (destruct i as [|i];[split;[vm_compute;reflexivity|vm_compute;lia]|]);lia. Qed.
Lemma reference_immediate_member i : (i < 304)%coq_nat ->
 List.In (reference_immediate_node i,reference_immediate_expression i) (reference_immediate_nodes i).
Proof. intro Bound.
 destruct i as [|i];[exact reference_control_member_1942|].
 destruct i as [|i];[exact reference_control_member_1943|].
 destruct i as [|i];[exact reference_control_member_1947|].
 destruct i as [|i];[exact reference_control_member_1948|].
 destruct i as [|i];[exact reference_control_member_1952|].
 destruct i as [|i];[exact reference_control_member_1953|].
 destruct i as [|i];[exact reference_control_member_1975|].
 destruct i as [|i];[exact reference_control_member_1976|].
 destruct i as [|i];[exact reference_control_member_1977|].
 destruct i as [|i];[exact reference_control_member_1981|].
 destruct i as [|i];[exact reference_control_member_1982|].
 destruct i as [|i];[exact reference_control_member_1983|].
 destruct i as [|i];[exact reference_control_member_1987|].
 destruct i as [|i];[exact reference_control_member_1988|].
 destruct i as [|i];[exact reference_control_member_1989|].
 destruct i as [|i];[exact reference_control_member_1993|].
 destruct i as [|i];[exact reference_control_member_1994|].
 destruct i as [|i];[exact reference_control_member_1995|].
 destruct i as [|i];[exact reference_control_member_1999|].
 destruct i as [|i];[exact reference_control_member_2000|].
 destruct i as [|i];[exact reference_control_member_2001|].
 destruct i as [|i];[exact reference_control_member_2005|].
 destruct i as [|i];[exact reference_control_member_2006|].
 destruct i as [|i];[exact reference_control_member_2007|].
 destruct i as [|i];[exact reference_control_member_2211|].
 destruct i as [|i];[exact reference_control_member_2212|].
 destruct i as [|i];[exact reference_control_member_2213|].
 destruct i as [|i];[exact reference_control_member_2214|].
 destruct i as [|i];[exact reference_control_member_2215|].
 destruct i as [|i];[exact reference_control_member_2216|].
 destruct i as [|i];[exact reference_control_member_2217|].
 destruct i as [|i];[exact reference_control_member_2218|].
 destruct i as [|i];[exact reference_control_member_2219|].
 destruct i as [|i];[exact reference_control_member_2220|].
 destruct i as [|i];[exact reference_control_member_2221|].
 destruct i as [|i];[exact reference_control_member_2222|].
 destruct i as [|i];[exact reference_control_member_2223|].
 destruct i as [|i];[exact reference_control_member_2224|].
 destruct i as [|i];[exact reference_control_member_2225|].
 destruct i as [|i];[exact reference_control_member_2226|].
 destruct i as [|i];[exact reference_control_member_2227|].
 destruct i as [|i];[exact reference_control_member_2228|].
 destruct i as [|i];[exact reference_control_member_2229|].
 destruct i as [|i];[exact reference_control_member_2230|].
 destruct i as [|i];[exact reference_control_member_2231|].
 destruct i as [|i];[exact reference_control_member_2232|].
 destruct i as [|i];[exact reference_control_member_2233|].
 destruct i as [|i];[exact reference_control_member_2234|].
 destruct i as [|i];[exact reference_control_member_2235|].
 destruct i as [|i];[exact reference_control_member_2236|].
 destruct i as [|i];[exact reference_control_member_2237|].
 destruct i as [|i];[exact reference_control_member_2238|].
 destruct i as [|i];[exact reference_control_member_2239|].
 destruct i as [|i];[exact reference_control_member_2240|].
 destruct i as [|i];[exact reference_control_member_2241|].
 destruct i as [|i];[exact reference_control_member_2242|].
 destruct i as [|i];[exact reference_control_member_2243|].
 destruct i as [|i];[exact reference_control_member_2244|].
 destruct i as [|i];[exact reference_control_member_2245|].
 destruct i as [|i];[exact reference_control_member_2246|].
 destruct i as [|i];[exact reference_control_member_2247|].
 destruct i as [|i];[exact reference_control_member_2248|].
 destruct i as [|i];[exact reference_control_member_2251|].
 destruct i as [|i];[exact reference_control_member_2252|].
 destruct i as [|i];[exact reference_control_member_2255|].
 destruct i as [|i];[exact reference_control_member_2256|].
 destruct i as [|i];[exact reference_control_member_2259|].
 destruct i as [|i];[exact reference_control_member_2260|].
 destruct i as [|i];[exact reference_control_member_2261|].
 destruct i as [|i];[exact reference_control_member_2262|].
 destruct i as [|i];[exact reference_control_member_2263|].
 destruct i as [|i];[exact reference_control_member_2264|].
 destruct i as [|i];[exact reference_control_member_2265|].
 destruct i as [|i];[exact reference_control_member_2266|].
 destruct i as [|i];[exact reference_control_member_2267|].
 destruct i as [|i];[exact reference_control_member_2268|].
 destruct i as [|i];[exact reference_control_member_2269|].
 destruct i as [|i];[exact reference_control_member_2270|].
 destruct i as [|i];[exact reference_control_member_2271|].
 destruct i as [|i];[exact reference_control_member_2272|].
 destruct i as [|i];[exact reference_control_member_2273|].
 destruct i as [|i];[exact reference_control_member_2274|].
 destruct i as [|i];[exact reference_control_member_2275|].
 destruct i as [|i];[exact reference_control_member_2276|].
 destruct i as [|i];[exact reference_control_member_2277|].
 destruct i as [|i];[exact reference_control_member_2278|].
 destruct i as [|i];[exact reference_control_member_2279|].
 destruct i as [|i];[exact reference_control_member_2280|].
 destruct i as [|i];[exact reference_control_member_2281|].
 destruct i as [|i];[exact reference_control_member_2282|].
 destruct i as [|i];[exact reference_control_member_2283|].
 destruct i as [|i];[exact reference_control_member_2286|].
 destruct i as [|i];[exact reference_control_member_2287|].
 destruct i as [|i];[exact reference_control_member_2288|].
 destruct i as [|i];[exact reference_control_member_2291|].
 destruct i as [|i];[exact reference_control_member_2292|].
 destruct i as [|i];[exact reference_control_member_2293|].
 destruct i as [|i];[exact reference_control_member_2296|].
 destruct i as [|i];[exact reference_control_member_2297|].
 destruct i as [|i];[exact reference_control_member_2300|].
 destruct i as [|i];[exact reference_control_member_2301|].
 destruct i as [|i];[exact reference_control_member_2304|].
 destruct i as [|i];[exact reference_control_member_2305|].
 destruct i as [|i];[exact reference_control_member_2308|].
 destruct i as [|i];[exact reference_control_member_2309|].
 destruct i as [|i];[exact reference_control_member_2312|].
 destruct i as [|i];[exact reference_control_member_2313|].
 destruct i as [|i];[exact reference_control_member_2316|].
 destruct i as [|i];[exact reference_control_member_2317|].
 destruct i as [|i];[exact reference_control_member_2318|].
 destruct i as [|i];[exact reference_control_member_2319|].
 destruct i as [|i];[exact reference_control_member_2320|].
 destruct i as [|i];[exact reference_control_member_2321|].
 destruct i as [|i];[exact reference_control_member_2322|].
 destruct i as [|i];[exact reference_control_member_2323|].
 destruct i as [|i];[exact reference_control_member_2324|].
 destruct i as [|i];[exact reference_control_member_2325|].
 destruct i as [|i];[exact reference_control_member_2326|].
 destruct i as [|i];[exact reference_control_member_2327|].
 destruct i as [|i];[exact reference_control_member_2328|].
 destruct i as [|i];[exact reference_control_member_2329|].
 destruct i as [|i];[exact reference_control_member_2330|].
 destruct i as [|i];[exact reference_control_member_2331|].
 destruct i as [|i];[exact reference_control_member_2332|].
 destruct i as [|i];[exact reference_control_member_2333|].
 destruct i as [|i];[exact reference_control_member_2334|].
 destruct i as [|i];[exact reference_control_member_2335|].
 destruct i as [|i];[exact reference_control_member_2336|].
 destruct i as [|i];[exact reference_control_member_2337|].
 destruct i as [|i];[exact reference_control_member_2338|].
 destruct i as [|i];[exact reference_control_member_2339|].
 destruct i as [|i];[exact reference_control_member_2340|].
 destruct i as [|i];[exact reference_control_member_2341|].
 destruct i as [|i];[exact reference_control_member_2342|].
 destruct i as [|i];[exact reference_control_member_2343|].
 destruct i as [|i];[exact reference_control_member_2344|].
 destruct i as [|i];[exact reference_control_member_2345|].
 destruct i as [|i];[exact reference_control_member_2346|].
 destruct i as [|i];[exact reference_control_member_2347|].
 destruct i as [|i];[exact reference_control_member_2348|].
 destruct i as [|i];[exact reference_control_member_2349|].
 destruct i as [|i];[exact reference_control_member_2350|].
 destruct i as [|i];[exact reference_control_member_2351|].
 destruct i as [|i];[exact reference_control_member_2352|].
 destruct i as [|i];[exact reference_control_member_2353|].
 destruct i as [|i];[exact reference_control_member_2354|].
 destruct i as [|i];[exact reference_control_member_2355|].
 destruct i as [|i];[exact reference_control_member_2358|].
 destruct i as [|i];[exact reference_control_member_2359|].
 destruct i as [|i];[exact reference_control_member_2360|].
 destruct i as [|i];[exact reference_control_member_2361|].
 destruct i as [|i];[exact reference_control_member_2362|].
 destruct i as [|i];[exact reference_control_member_2363|].
 destruct i as [|i];[exact reference_control_member_2364|].
 destruct i as [|i];[exact reference_control_member_2365|].
 destruct i as [|i];[exact reference_control_member_2366|].
 destruct i as [|i];[exact reference_control_member_2367|].
 destruct i as [|i];[exact reference_control_member_2368|].
 destruct i as [|i];[exact reference_control_member_2369|].
 destruct i as [|i];[exact reference_control_member_2370|].
 destruct i as [|i];[exact reference_control_member_2371|].
 destruct i as [|i];[exact reference_control_member_2372|].
 destruct i as [|i];[exact reference_control_member_2373|].
 destruct i as [|i];[exact reference_control_member_2374|].
 destruct i as [|i];[exact reference_control_member_2375|].
 destruct i as [|i];[exact reference_control_member_2376|].
 destruct i as [|i];[exact reference_control_member_2377|].
 destruct i as [|i];[exact reference_control_member_2378|].
 destruct i as [|i];[exact reference_control_member_2379|].
 destruct i as [|i];[exact reference_control_member_2380|].
 destruct i as [|i];[exact reference_control_member_2381|].
 destruct i as [|i];[exact reference_control_member_2382|].
 destruct i as [|i];[exact reference_control_member_2383|].
 destruct i as [|i];[exact reference_control_member_2384|].
 destruct i as [|i];[exact reference_control_member_2385|].
 destruct i as [|i];[exact reference_control_member_2386|].
 destruct i as [|i];[exact reference_control_member_2387|].
 destruct i as [|i];[exact reference_control_member_2388|].
 destruct i as [|i];[exact reference_control_member_2389|].
 destruct i as [|i];[exact reference_control_member_2390|].
 destruct i as [|i];[exact reference_control_member_2391|].
 destruct i as [|i];[exact reference_control_member_2392|].
 destruct i as [|i];[exact reference_control_member_2393|].
 destruct i as [|i];[exact reference_control_member_2394|].
 destruct i as [|i];[exact reference_control_member_2395|].
 destruct i as [|i];[exact reference_control_member_2396|].
 destruct i as [|i];[exact reference_control_member_2397|].
 destruct i as [|i];[exact reference_control_member_2398|].
 destruct i as [|i];[exact reference_control_member_2399|].
 destruct i as [|i];[exact reference_control_member_2400|].
 destruct i as [|i];[exact reference_control_member_2401|].
 destruct i as [|i];[exact reference_control_member_2404|].
 destruct i as [|i];[exact reference_control_member_2405|].
 destruct i as [|i];[exact reference_control_member_2406|].
 destruct i as [|i];[exact reference_control_member_2407|].
 destruct i as [|i];[exact reference_control_member_2408|].
 destruct i as [|i];[exact reference_control_member_2409|].
 destruct i as [|i];[exact reference_control_member_2412|].
 destruct i as [|i];[exact reference_control_member_2413|].
 destruct i as [|i];[exact reference_control_member_2414|].
 destruct i as [|i];[exact reference_control_member_2415|].
 destruct i as [|i];[exact reference_control_member_2416|].
 destruct i as [|i];[exact reference_control_member_2417|].
 destruct i as [|i];[exact reference_control_member_2420|].
 destruct i as [|i];[exact reference_control_member_2421|].
 destruct i as [|i];[exact reference_control_member_2422|].
 destruct i as [|i];[exact reference_control_member_2423|].
 destruct i as [|i];[exact reference_control_member_2424|].
 destruct i as [|i];[exact reference_control_member_2425|].
 destruct i as [|i];[exact reference_control_member_2428|].
 destruct i as [|i];[exact reference_control_member_2429|].
 destruct i as [|i];[exact reference_control_member_2430|].
 destruct i as [|i];[exact reference_control_member_2431|].
 destruct i as [|i];[exact reference_control_member_2432|].
 destruct i as [|i];[exact reference_control_member_2433|].
 destruct i as [|i];[exact reference_control_member_2436|].
 destruct i as [|i];[exact reference_control_member_2437|].
 destruct i as [|i];[exact reference_control_member_2438|].
 destruct i as [|i];[exact reference_control_member_2439|].
 destruct i as [|i];[exact reference_control_member_2440|].
 destruct i as [|i];[exact reference_control_member_2441|].
 destruct i as [|i];[exact reference_control_member_2444|].
 destruct i as [|i];[exact reference_control_member_2445|].
 destruct i as [|i];[exact reference_control_member_2448|].
 destruct i as [|i];[exact reference_control_member_2449|].
 destruct i as [|i];[exact reference_control_member_2450|].
 destruct i as [|i];[exact reference_control_member_2451|].
 destruct i as [|i];[exact reference_control_member_2452|].
 destruct i as [|i];[exact reference_control_member_2453|].
 destruct i as [|i];[exact reference_control_member_2454|].
 destruct i as [|i];[exact reference_control_member_2455|].
 destruct i as [|i];[exact reference_control_member_2456|].
 destruct i as [|i];[exact reference_control_member_2457|].
 destruct i as [|i];[exact reference_control_member_2458|].
 destruct i as [|i];[exact reference_control_member_2459|].
 destruct i as [|i];[exact reference_control_member_2460|].
 destruct i as [|i];[exact reference_control_member_2461|].
 destruct i as [|i];[exact reference_control_member_2462|].
 destruct i as [|i];[exact reference_control_member_2463|].
 destruct i as [|i];[exact reference_control_member_2464|].
 destruct i as [|i];[exact reference_control_member_2465|].
 destruct i as [|i];[exact reference_control_member_2466|].
 destruct i as [|i];[exact reference_control_member_2469|].
 destruct i as [|i];[exact reference_control_member_2470|].
 destruct i as [|i];[exact reference_control_member_2473|].
 destruct i as [|i];[exact reference_control_member_2476|].
 destruct i as [|i];[exact reference_control_member_2477|].
 destruct i as [|i];[exact reference_control_member_2478|].
 destruct i as [|i];[exact reference_control_member_2479|].
 destruct i as [|i];[exact reference_control_member_2480|].
 destruct i as [|i];[exact reference_control_member_2481|].
 destruct i as [|i];[exact reference_control_member_2482|].
 destruct i as [|i];[exact reference_control_member_2483|].
 destruct i as [|i];[exact reference_control_member_2484|].
 destruct i as [|i];[exact reference_control_member_2487|].
 destruct i as [|i];[exact reference_control_member_2488|].
 destruct i as [|i];[exact reference_control_member_2491|].
 destruct i as [|i];[exact reference_control_member_2492|].
 destruct i as [|i];[exact reference_control_member_2495|].
 destruct i as [|i];[exact reference_control_member_2496|].
 destruct i as [|i];[exact reference_control_member_2499|].
 destruct i as [|i];[exact reference_control_member_2500|].
 destruct i as [|i];[exact reference_control_member_2503|].
 destruct i as [|i];[exact reference_control_member_2504|].
 destruct i as [|i];[exact reference_control_member_2507|].
 destruct i as [|i];[exact reference_control_member_2508|].
 destruct i as [|i];[exact reference_control_member_2511|].
 destruct i as [|i];[exact reference_control_member_2512|].
 destruct i as [|i];[exact reference_control_member_2515|].
 destruct i as [|i];[exact reference_control_member_2516|].
 destruct i as [|i];[exact reference_control_member_2519|].
 destruct i as [|i];[exact reference_control_member_2520|].
 destruct i as [|i];[exact reference_control_member_2521|].
 destruct i as [|i];[exact reference_control_member_2522|].
 destruct i as [|i];[exact reference_control_member_2523|].
 destruct i as [|i];[exact reference_control_member_2524|].
 destruct i as [|i];[exact reference_control_member_2525|].
 destruct i as [|i];[exact reference_control_member_2526|].
 destruct i as [|i];[exact reference_control_member_2527|].
 destruct i as [|i];[exact reference_control_member_2528|].
 destruct i as [|i];[exact reference_control_member_2529|].
 destruct i as [|i];[exact reference_control_member_2530|].
 destruct i as [|i];[exact reference_control_member_2531|].
 destruct i as [|i];[exact reference_control_member_2532|].
 destruct i as [|i];[exact reference_control_member_2533|].
 destruct i as [|i];[exact reference_control_member_2534|].
 destruct i as [|i];[exact reference_control_member_2535|].
 destruct i as [|i];[exact reference_control_member_2536|].
 destruct i as [|i];[exact reference_control_member_2537|].
 destruct i as [|i];[exact reference_control_member_2538|].
 destruct i as [|i];[exact reference_control_member_2539|].
 destruct i as [|i];[exact reference_control_member_2540|].
 destruct i as [|i];[exact reference_control_member_2541|].
 destruct i as [|i];[exact reference_control_member_2542|].
 destruct i as [|i];[exact reference_control_member_2543|].
 destruct i as [|i];[exact reference_control_member_2544|].
 destruct i as [|i];[exact reference_control_member_2545|].
 destruct i as [|i];[exact reference_control_member_2546|].
 destruct i as [|i];[exact reference_control_member_2547|].
 destruct i as [|i];[exact reference_control_member_2548|].
 destruct i as [|i];[exact reference_control_member_2549|].
 destruct i as [|i];[exact reference_control_member_2550|].
 destruct i as [|i];[exact reference_control_member_2551|].
 destruct i as [|i];[exact reference_control_member_2552|].
 lia.
Qed.
Lemma reference_immediate_predecessors i node : (i < 304)%coq_nat -> List.In node (reference_immediate_refs i) ->
 node = 1884 \/ exists j, (j < i)%coq_nat /\ (j < 304)%coq_nat /\ reference_immediate_node j = node /\ reference_immediate_width_of node = reference_immediate_width j /\ (reference_immediate_rank j < reference_immediate_rank i)%coq_nat.
Proof.
 intro Bound.
 destruct i as [|i].
 { cbn [reference_immediate_refs reference_immediate_dependencies nth List.In].
 intro Member.
 destruct Member as [<-|Member].
 - left;reflexivity.
 - contradiction. }
 destruct i as [|i].
 { cbn [reference_immediate_refs reference_immediate_dependencies nth List.In].
 intro Member.
 destruct Member as [<-|Member].
 - right;exists 0%nat;vm_compute;repeat split;try reflexivity;lia.
 - contradiction. }
 destruct i as [|i].
 { cbn [reference_immediate_refs reference_immediate_dependencies nth List.In].
 intro Member.
 destruct Member as [<-|Member].
 - left;reflexivity.
 - contradiction. }
 destruct i as [|i].
 { cbn [reference_immediate_refs reference_immediate_dependencies nth List.In].
 intro Member.
 destruct Member as [<-|Member].
 - right;exists 2%nat;vm_compute;repeat split;try reflexivity;lia.
 - contradiction. }
 destruct i as [|i].
 { cbn [reference_immediate_refs reference_immediate_dependencies nth List.In].
 intro Member.
 destruct Member as [<-|Member].
 - left;reflexivity.
 - contradiction. }
 destruct i as [|i].
 { cbn [reference_immediate_refs reference_immediate_dependencies nth List.In].
 intro Member.
 destruct Member as [<-|Member].
 - right;exists 4%nat;vm_compute;repeat split;try reflexivity;lia.
 - contradiction. }
 destruct i as [|i].
 { cbn [reference_immediate_refs reference_immediate_dependencies nth List.In].
 intro Member.
 destruct Member as [<-|Member].
 - left;reflexivity.
 - contradiction. }
 destruct i as [|i].
 { cbn [reference_immediate_refs reference_immediate_dependencies nth List.In].
 intro Member.
 destruct Member as [<-|Member].
 - right;exists 6%nat;vm_compute;repeat split;try reflexivity;lia.
 - contradiction. }
 destruct i as [|i].
 { cbn [reference_immediate_refs reference_immediate_dependencies nth List.In].
 intro Member.
 destruct Member as [<-|Member].
 - right;exists 7%nat;vm_compute;repeat split;try reflexivity;lia.
 - contradiction. }
 destruct i as [|i].
 { cbn [reference_immediate_refs reference_immediate_dependencies nth List.In].
 intro Member.
 destruct Member as [<-|Member].
 - left;reflexivity.
 - contradiction. }
 destruct i as [|i].
 { cbn [reference_immediate_refs reference_immediate_dependencies nth List.In].
 intro Member.
 destruct Member as [<-|Member].
 - right;exists 9%nat;vm_compute;repeat split;try reflexivity;lia.
 - contradiction. }
 destruct i as [|i].
 { cbn [reference_immediate_refs reference_immediate_dependencies nth List.In].
 intro Member.
 destruct Member as [<-|Member].
 - right;exists 10%nat;vm_compute;repeat split;try reflexivity;lia.
 - contradiction. }
 destruct i as [|i].
 { cbn [reference_immediate_refs reference_immediate_dependencies nth List.In].
 intro Member.
 destruct Member as [<-|Member].
 - left;reflexivity.
 - contradiction. }
 destruct i as [|i].
 { cbn [reference_immediate_refs reference_immediate_dependencies nth List.In].
 intro Member.
 destruct Member as [<-|Member].
 - right;exists 12%nat;vm_compute;repeat split;try reflexivity;lia.
 - contradiction. }
 destruct i as [|i].
 { cbn [reference_immediate_refs reference_immediate_dependencies nth List.In].
 intro Member.
 destruct Member as [<-|Member].
 - right;exists 13%nat;vm_compute;repeat split;try reflexivity;lia.
 - contradiction. }
 destruct i as [|i].
 { cbn [reference_immediate_refs reference_immediate_dependencies nth List.In].
 intro Member.
 destruct Member as [<-|Member].
 - left;reflexivity.
 - contradiction. }
 destruct i as [|i].
 { cbn [reference_immediate_refs reference_immediate_dependencies nth List.In].
 intro Member.
 destruct Member as [<-|Member].
 - right;exists 15%nat;vm_compute;repeat split;try reflexivity;lia.
 - contradiction. }
 destruct i as [|i].
 { cbn [reference_immediate_refs reference_immediate_dependencies nth List.In].
 intro Member.
 destruct Member as [<-|Member].
 - right;exists 16%nat;vm_compute;repeat split;try reflexivity;lia.
 - contradiction. }
 destruct i as [|i].
 { cbn [reference_immediate_refs reference_immediate_dependencies nth List.In].
 intro Member.
 destruct Member as [<-|Member].
 - left;reflexivity.
 - contradiction. }
 destruct i as [|i].
 { cbn [reference_immediate_refs reference_immediate_dependencies nth List.In].
 intro Member.
 destruct Member as [<-|Member].
 - right;exists 18%nat;vm_compute;repeat split;try reflexivity;lia.
 - contradiction. }
 destruct i as [|i].
 { cbn [reference_immediate_refs reference_immediate_dependencies nth List.In].
 intro Member.
 destruct Member as [<-|Member].
 - right;exists 19%nat;vm_compute;repeat split;try reflexivity;lia.
 - contradiction. }
 destruct i as [|i].
 { cbn [reference_immediate_refs reference_immediate_dependencies nth List.In].
 intro Member.
 destruct Member as [<-|Member].
 - left;reflexivity.
 - contradiction. }
 destruct i as [|i].
 { cbn [reference_immediate_refs reference_immediate_dependencies nth List.In].
 intro Member.
 destruct Member as [<-|Member].
 - right;exists 21%nat;vm_compute;repeat split;try reflexivity;lia.
 - contradiction. }
 destruct i as [|i].
 { cbn [reference_immediate_refs reference_immediate_dependencies nth List.In].
 intro Member.
 destruct Member as [<-|Member].
 - right;exists 22%nat;vm_compute;repeat split;try reflexivity;lia.
 - contradiction. }
 destruct i as [|i].
 { cbn [reference_immediate_refs reference_immediate_dependencies nth List.In].
 intro Member.
 destruct Member as [<-|Member].
 - left;reflexivity.
 - contradiction. }
 destruct i as [|i].
 { cbn [reference_immediate_refs reference_immediate_dependencies nth List.In].
 intro Member.
 destruct Member as [<-|Member].
 - left;reflexivity.
 - contradiction. }
 destruct i as [|i].
 { cbn [reference_immediate_refs reference_immediate_dependencies nth List.In].
 intro Member.
 destruct Member as [<-|Member].
 - left;reflexivity.
 - contradiction. }
 destruct i as [|i].
 { cbn [reference_immediate_refs reference_immediate_dependencies nth List.In].
 intro Member.
 destruct Member as [<-|Member].
 - left;reflexivity.
 - contradiction. }
 destruct i as [|i].
 { cbn [reference_immediate_refs reference_immediate_dependencies nth List.In].
 intro Member.
 destruct Member as [<-|Member].
 - left;reflexivity.
 - contradiction. }
 destruct i as [|i].
 { cbn [reference_immediate_refs reference_immediate_dependencies nth List.In].
 intro Member.
 destruct Member as [<-|Member].
 - left;reflexivity.
 - contradiction. }
 destruct i as [|i].
 { cbn [reference_immediate_refs reference_immediate_dependencies nth List.In].
 intro Member.
 destruct Member as [<-|Member].
 - left;reflexivity.
 - contradiction. }
 destruct i as [|i].
 { cbn [reference_immediate_refs reference_immediate_dependencies nth List.In].
 intro Member.
 destruct Member as [<-|Member].
 - left;reflexivity.
 - contradiction. }
 destruct i as [|i].
 { cbn [reference_immediate_refs reference_immediate_dependencies nth List.In].
 intro Member.
 destruct Member as [<-|Member].
 - left;reflexivity.
 - contradiction. }
 destruct i as [|i].
 { cbn [reference_immediate_refs reference_immediate_dependencies nth List.In].
 intro Member.
 destruct Member as [<-|Member].
 - left;reflexivity.
 - contradiction. }
 destruct i as [|i].
 { cbn [reference_immediate_refs reference_immediate_dependencies nth List.In].
 intro Member.
 destruct Member as [<-|Member].
 - left;reflexivity.
 - contradiction. }
 destruct i as [|i].
 { cbn [reference_immediate_refs reference_immediate_dependencies nth List.In].
 intro Member.
 destruct Member as [<-|Member].
 - left;reflexivity.
 - contradiction. }
 destruct i as [|i].
 { cbn [reference_immediate_refs reference_immediate_dependencies nth List.In].
 intro Member.
 destruct Member as [<-|Member].
 - left;reflexivity.
 - contradiction. }
 destruct i as [|i].
 { cbn [reference_immediate_refs reference_immediate_dependencies nth List.In].
 intro Member.
 destruct Member as [<-|Member].
 - left;reflexivity.
 - contradiction. }
 destruct i as [|i].
 { cbn [reference_immediate_refs reference_immediate_dependencies nth List.In].
 intro Member.
 destruct Member as [<-|Member].
 - left;reflexivity.
 - contradiction. }
 destruct i as [|i].
 { cbn [reference_immediate_refs reference_immediate_dependencies nth List.In].
 intro Member.
 destruct Member as [<-|Member].
 - left;reflexivity.
 - contradiction. }
 destruct i as [|i].
 { cbn [reference_immediate_refs reference_immediate_dependencies nth List.In].
 intro Member.
 destruct Member as [<-|Member].
 - left;reflexivity.
 - contradiction. }
 destruct i as [|i].
 { cbn [reference_immediate_refs reference_immediate_dependencies nth List.In].
 intro Member.
 destruct Member as [<-|Member].
 - left;reflexivity.
 - contradiction. }
 destruct i as [|i].
 { cbn [reference_immediate_refs reference_immediate_dependencies nth List.In].
 intro Member.
 destruct Member as [<-|Member].
 - right;exists 41%nat;vm_compute;repeat split;try reflexivity;lia.
 - contradiction. }
 destruct i as [|i].
 { cbn [reference_immediate_refs reference_immediate_dependencies nth List.In].
 intro Member.
 destruct Member as [<-|Member].
 - right;exists 40%nat;vm_compute;repeat split;try reflexivity;lia.
 destruct Member as [<-|Member].
 - right;exists 42%nat;vm_compute;repeat split;try reflexivity;lia.
 - contradiction. }
 destruct i as [|i].
 { cbn [reference_immediate_refs reference_immediate_dependencies nth List.In].
 intro Member.
 destruct Member as [<-|Member].
 - right;exists 39%nat;vm_compute;repeat split;try reflexivity;lia.
 destruct Member as [<-|Member].
 - right;exists 43%nat;vm_compute;repeat split;try reflexivity;lia.
 - contradiction. }
 destruct i as [|i].
 { cbn [reference_immediate_refs reference_immediate_dependencies nth List.In].
 intro Member.
 destruct Member as [<-|Member].
 - right;exists 38%nat;vm_compute;repeat split;try reflexivity;lia.
 destruct Member as [<-|Member].
 - right;exists 44%nat;vm_compute;repeat split;try reflexivity;lia.
 - contradiction. }
 destruct i as [|i].
 { cbn [reference_immediate_refs reference_immediate_dependencies nth List.In].
 intro Member.
 destruct Member as [<-|Member].
 - right;exists 37%nat;vm_compute;repeat split;try reflexivity;lia.
 destruct Member as [<-|Member].
 - right;exists 45%nat;vm_compute;repeat split;try reflexivity;lia.
 - contradiction. }
 destruct i as [|i].
 { cbn [reference_immediate_refs reference_immediate_dependencies nth List.In].
 intro Member.
 destruct Member as [<-|Member].
 - right;exists 36%nat;vm_compute;repeat split;try reflexivity;lia.
 destruct Member as [<-|Member].
 - right;exists 46%nat;vm_compute;repeat split;try reflexivity;lia.
 - contradiction. }
 destruct i as [|i].
 { cbn [reference_immediate_refs reference_immediate_dependencies nth List.In].
 intro Member.
 destruct Member as [<-|Member].
 - right;exists 35%nat;vm_compute;repeat split;try reflexivity;lia.
 destruct Member as [<-|Member].
 - right;exists 47%nat;vm_compute;repeat split;try reflexivity;lia.
 - contradiction. }
 destruct i as [|i].
 { cbn [reference_immediate_refs reference_immediate_dependencies nth List.In].
 intro Member.
 destruct Member as [<-|Member].
 - right;exists 34%nat;vm_compute;repeat split;try reflexivity;lia.
 destruct Member as [<-|Member].
 - right;exists 48%nat;vm_compute;repeat split;try reflexivity;lia.
 - contradiction. }
 destruct i as [|i].
 { cbn [reference_immediate_refs reference_immediate_dependencies nth List.In].
 intro Member.
 destruct Member as [<-|Member].
 - right;exists 33%nat;vm_compute;repeat split;try reflexivity;lia.
 destruct Member as [<-|Member].
 - right;exists 49%nat;vm_compute;repeat split;try reflexivity;lia.
 - contradiction. }
 destruct i as [|i].
 { cbn [reference_immediate_refs reference_immediate_dependencies nth List.In].
 intro Member.
 destruct Member as [<-|Member].
 - right;exists 32%nat;vm_compute;repeat split;try reflexivity;lia.
 destruct Member as [<-|Member].
 - right;exists 50%nat;vm_compute;repeat split;try reflexivity;lia.
 - contradiction. }
 destruct i as [|i].
 { cbn [reference_immediate_refs reference_immediate_dependencies nth List.In].
 intro Member.
 destruct Member as [<-|Member].
 - right;exists 31%nat;vm_compute;repeat split;try reflexivity;lia.
 destruct Member as [<-|Member].
 - right;exists 51%nat;vm_compute;repeat split;try reflexivity;lia.
 - contradiction. }
 destruct i as [|i].
 { cbn [reference_immediate_refs reference_immediate_dependencies nth List.In].
 intro Member.
 destruct Member as [<-|Member].
 - right;exists 30%nat;vm_compute;repeat split;try reflexivity;lia.
 destruct Member as [<-|Member].
 - right;exists 52%nat;vm_compute;repeat split;try reflexivity;lia.
 - contradiction. }
 destruct i as [|i].
 { cbn [reference_immediate_refs reference_immediate_dependencies nth List.In].
 intro Member.
 destruct Member as [<-|Member].
 - right;exists 29%nat;vm_compute;repeat split;try reflexivity;lia.
 destruct Member as [<-|Member].
 - right;exists 53%nat;vm_compute;repeat split;try reflexivity;lia.
 - contradiction. }
 destruct i as [|i].
 { cbn [reference_immediate_refs reference_immediate_dependencies nth List.In].
 intro Member.
 destruct Member as [<-|Member].
 - right;exists 28%nat;vm_compute;repeat split;try reflexivity;lia.
 destruct Member as [<-|Member].
 - right;exists 54%nat;vm_compute;repeat split;try reflexivity;lia.
 - contradiction. }
 destruct i as [|i].
 { cbn [reference_immediate_refs reference_immediate_dependencies nth List.In].
 intro Member.
 destruct Member as [<-|Member].
 - right;exists 27%nat;vm_compute;repeat split;try reflexivity;lia.
 destruct Member as [<-|Member].
 - right;exists 55%nat;vm_compute;repeat split;try reflexivity;lia.
 - contradiction. }
 destruct i as [|i].
 { cbn [reference_immediate_refs reference_immediate_dependencies nth List.In].
 intro Member.
 destruct Member as [<-|Member].
 - right;exists 26%nat;vm_compute;repeat split;try reflexivity;lia.
 destruct Member as [<-|Member].
 - right;exists 56%nat;vm_compute;repeat split;try reflexivity;lia.
 - contradiction. }
 destruct i as [|i].
 { cbn [reference_immediate_refs reference_immediate_dependencies nth List.In].
 intro Member.
 destruct Member as [<-|Member].
 - right;exists 25%nat;vm_compute;repeat split;try reflexivity;lia.
 destruct Member as [<-|Member].
 - right;exists 57%nat;vm_compute;repeat split;try reflexivity;lia.
 - contradiction. }
 destruct i as [|i].
 { cbn [reference_immediate_refs reference_immediate_dependencies nth List.In].
 intro Member.
 destruct Member as [<-|Member].
 - right;exists 24%nat;vm_compute;repeat split;try reflexivity;lia.
 destruct Member as [<-|Member].
 - right;exists 58%nat;vm_compute;repeat split;try reflexivity;lia.
 - contradiction. }
 destruct i as [|i].
 { cbn [reference_immediate_refs reference_immediate_dependencies nth List.In].
 intro Member.
 destruct Member as [<-|Member].
 - right;exists 59%nat;vm_compute;repeat split;try reflexivity;lia.
 - contradiction. }
 destruct i as [|i].
 { cbn [reference_immediate_refs reference_immediate_dependencies nth List.In].
 intro Member.
 destruct Member as [<-|Member].
 - right;exists 60%nat;vm_compute;repeat split;try reflexivity;lia.
 - contradiction. }
 destruct i as [|i].
 { cbn [reference_immediate_refs reference_immediate_dependencies nth List.In].
 contradiction. }
 destruct i as [|i].
 { cbn [reference_immediate_refs reference_immediate_dependencies nth List.In].
 intro Member.
 destruct Member as [<-|Member].
 - right;exists 62%nat;vm_compute;repeat split;try reflexivity;lia.
 destruct Member as [<-|Member].
 - right;exists 61%nat;vm_compute;repeat split;try reflexivity;lia.
 - contradiction. }
 destruct i as [|i].
 { cbn [reference_immediate_refs reference_immediate_dependencies nth List.In].
 contradiction. }
 destruct i as [|i].
 { cbn [reference_immediate_refs reference_immediate_dependencies nth List.In].
 intro Member.
 destruct Member as [<-|Member].
 - right;exists 64%nat;vm_compute;repeat split;try reflexivity;lia.
 destruct Member as [<-|Member].
 - right;exists 61%nat;vm_compute;repeat split;try reflexivity;lia.
 - contradiction. }
 destruct i as [|i].
 { cbn [reference_immediate_refs reference_immediate_dependencies nth List.In].
 contradiction. }
 destruct i as [|i].
 { cbn [reference_immediate_refs reference_immediate_dependencies nth List.In].
 intro Member.
 destruct Member as [<-|Member].
 - right;exists 66%nat;vm_compute;repeat split;try reflexivity;lia.
 destruct Member as [<-|Member].
 - right;exists 61%nat;vm_compute;repeat split;try reflexivity;lia.
 - contradiction. }
 destruct i as [|i].
 { cbn [reference_immediate_refs reference_immediate_dependencies nth List.In].
 intro Member.
 destruct Member as [<-|Member].
 - left;reflexivity.
 - contradiction. }
 destruct i as [|i].
 { cbn [reference_immediate_refs reference_immediate_dependencies nth List.In].
 intro Member.
 destruct Member as [<-|Member].
 - left;reflexivity.
 - contradiction. }
 destruct i as [|i].
 { cbn [reference_immediate_refs reference_immediate_dependencies nth List.In].
 intro Member.
 destruct Member as [<-|Member].
 - left;reflexivity.
 - contradiction. }
 destruct i as [|i].
 { cbn [reference_immediate_refs reference_immediate_dependencies nth List.In].
 intro Member.
 destruct Member as [<-|Member].
 - right;exists 70%nat;vm_compute;repeat split;try reflexivity;lia.
 - contradiction. }
 destruct i as [|i].
 { cbn [reference_immediate_refs reference_immediate_dependencies nth List.In].
 intro Member.
 destruct Member as [<-|Member].
 - right;exists 69%nat;vm_compute;repeat split;try reflexivity;lia.
 destruct Member as [<-|Member].
 - right;exists 71%nat;vm_compute;repeat split;try reflexivity;lia.
 - contradiction. }
 destruct i as [|i].
 { cbn [reference_immediate_refs reference_immediate_dependencies nth List.In].
 intro Member.
 destruct Member as [<-|Member].
 - right;exists 68%nat;vm_compute;repeat split;try reflexivity;lia.
 destruct Member as [<-|Member].
 - right;exists 72%nat;vm_compute;repeat split;try reflexivity;lia.
 - contradiction. }
 destruct i as [|i].
 { cbn [reference_immediate_refs reference_immediate_dependencies nth List.In].
 intro Member.
 destruct Member as [<-|Member].
 - right;exists 73%nat;vm_compute;repeat split;try reflexivity;lia.
 - contradiction. }
 destruct i as [|i].
 { cbn [reference_immediate_refs reference_immediate_dependencies nth List.In].
 intro Member.
 destruct Member as [<-|Member].
 - right;exists 74%nat;vm_compute;repeat split;try reflexivity;lia.
 - contradiction. }
 destruct i as [|i].
 { cbn [reference_immediate_refs reference_immediate_dependencies nth List.In].
 intro Member.
 destruct Member as [<-|Member].
 - right;exists 1%nat;vm_compute;repeat split;try reflexivity;lia.
 - contradiction. }
 destruct i as [|i].
 { cbn [reference_immediate_refs reference_immediate_dependencies nth List.In].
 intro Member.
 destruct Member as [<-|Member].
 - right;exists 76%nat;vm_compute;repeat split;try reflexivity;lia.
 - contradiction. }
 destruct i as [|i].
 { cbn [reference_immediate_refs reference_immediate_dependencies nth List.In].
 intro Member.
 destruct Member as [<-|Member].
 - right;exists 77%nat;vm_compute;repeat split;try reflexivity;lia.
 - contradiction. }
 destruct i as [|i].
 { cbn [reference_immediate_refs reference_immediate_dependencies nth List.In].
 intro Member.
 destruct Member as [<-|Member].
 - right;exists 3%nat;vm_compute;repeat split;try reflexivity;lia.
 - contradiction. }
 destruct i as [|i].
 { cbn [reference_immediate_refs reference_immediate_dependencies nth List.In].
 intro Member.
 destruct Member as [<-|Member].
 - right;exists 79%nat;vm_compute;repeat split;try reflexivity;lia.
 - contradiction. }
 destruct i as [|i].
 { cbn [reference_immediate_refs reference_immediate_dependencies nth List.In].
 intro Member.
 destruct Member as [<-|Member].
 - right;exists 80%nat;vm_compute;repeat split;try reflexivity;lia.
 - contradiction. }
 destruct i as [|i].
 { cbn [reference_immediate_refs reference_immediate_dependencies nth List.In].
 intro Member.
 destruct Member as [<-|Member].
 - right;exists 5%nat;vm_compute;repeat split;try reflexivity;lia.
 - contradiction. }
 destruct i as [|i].
 { cbn [reference_immediate_refs reference_immediate_dependencies nth List.In].
 intro Member.
 destruct Member as [<-|Member].
 - right;exists 82%nat;vm_compute;repeat split;try reflexivity;lia.
 - contradiction. }
 destruct i as [|i].
 { cbn [reference_immediate_refs reference_immediate_dependencies nth List.In].
 intro Member.
 destruct Member as [<-|Member].
 - right;exists 83%nat;vm_compute;repeat split;try reflexivity;lia.
 - contradiction. }
 destruct i as [|i].
 { cbn [reference_immediate_refs reference_immediate_dependencies nth List.In].
 intro Member.
 destruct Member as [<-|Member].
 - right;exists 84%nat;vm_compute;repeat split;try reflexivity;lia.
 - contradiction. }
 destruct i as [|i].
 { cbn [reference_immediate_refs reference_immediate_dependencies nth List.In].
 intro Member.
 destruct Member as [<-|Member].
 - right;exists 81%nat;vm_compute;repeat split;try reflexivity;lia.
 destruct Member as [<-|Member].
 - right;exists 85%nat;vm_compute;repeat split;try reflexivity;lia.
 - contradiction. }
 destruct i as [|i].
 { cbn [reference_immediate_refs reference_immediate_dependencies nth List.In].
 intro Member.
 destruct Member as [<-|Member].
 - right;exists 78%nat;vm_compute;repeat split;try reflexivity;lia.
 destruct Member as [<-|Member].
 - right;exists 86%nat;vm_compute;repeat split;try reflexivity;lia.
 - contradiction. }
 destruct i as [|i].
 { cbn [reference_immediate_refs reference_immediate_dependencies nth List.In].
 intro Member.
 destruct Member as [<-|Member].
 - right;exists 87%nat;vm_compute;repeat split;try reflexivity;lia.
 - contradiction. }
 destruct i as [|i].
 { cbn [reference_immediate_refs reference_immediate_dependencies nth List.In].
 intro Member.
 destruct Member as [<-|Member].
 - right;exists 88%nat;vm_compute;repeat split;try reflexivity;lia.
 - contradiction. }
 destruct i as [|i].
 { cbn [reference_immediate_refs reference_immediate_dependencies nth List.In].
 intro Member.
 destruct Member as [<-|Member].
 - right;exists 75%nat;vm_compute;repeat split;try reflexivity;lia.
 destruct Member as [<-|Member].
 - right;exists 89%nat;vm_compute;repeat split;try reflexivity;lia.
 - contradiction. }
 destruct i as [|i].
 { cbn [reference_immediate_refs reference_immediate_dependencies nth List.In].
 contradiction. }
 destruct i as [|i].
 { cbn [reference_immediate_refs reference_immediate_dependencies nth List.In].
 intro Member.
 destruct Member as [<-|Member].
 - right;exists 91%nat;vm_compute;repeat split;try reflexivity;lia.
 destruct Member as [<-|Member].
 - right;exists 90%nat;vm_compute;repeat split;try reflexivity;lia.
 - contradiction. }
 destruct i as [|i].
 { cbn [reference_immediate_refs reference_immediate_dependencies nth List.In].
 intro Member.
 destruct Member as [<-|Member].
 - right;exists 75%nat;vm_compute;repeat split;try reflexivity;lia.
 destruct Member as [<-|Member].
 - right;exists 89%nat;vm_compute;repeat split;try reflexivity;lia.
 - contradiction. }
 destruct i as [|i].
 { cbn [reference_immediate_refs reference_immediate_dependencies nth List.In].
 contradiction. }
 destruct i as [|i].
 { cbn [reference_immediate_refs reference_immediate_dependencies nth List.In].
 intro Member.
 destruct Member as [<-|Member].
 - right;exists 94%nat;vm_compute;repeat split;try reflexivity;lia.
 destruct Member as [<-|Member].
 - right;exists 93%nat;vm_compute;repeat split;try reflexivity;lia.
 - contradiction. }
 destruct i as [|i].
 { cbn [reference_immediate_refs reference_immediate_dependencies nth List.In].
 intro Member.
 destruct Member as [<-|Member].
 - right;exists 75%nat;vm_compute;repeat split;try reflexivity;lia.
 destruct Member as [<-|Member].
 - right;exists 89%nat;vm_compute;repeat split;try reflexivity;lia.
 - contradiction. }
 destruct i as [|i].
 { cbn [reference_immediate_refs reference_immediate_dependencies nth List.In].
 contradiction. }
 destruct i as [|i].
 { cbn [reference_immediate_refs reference_immediate_dependencies nth List.In].
 intro Member.
 destruct Member as [<-|Member].
 - right;exists 97%nat;vm_compute;repeat split;try reflexivity;lia.
 destruct Member as [<-|Member].
 - right;exists 96%nat;vm_compute;repeat split;try reflexivity;lia.
 - contradiction. }
 destruct i as [|i].
 { cbn [reference_immediate_refs reference_immediate_dependencies nth List.In].
 contradiction. }
 destruct i as [|i].
 { cbn [reference_immediate_refs reference_immediate_dependencies nth List.In].
 intro Member.
 destruct Member as [<-|Member].
 - right;exists 99%nat;vm_compute;repeat split;try reflexivity;lia.
 destruct Member as [<-|Member].
 - right;exists 61%nat;vm_compute;repeat split;try reflexivity;lia.
 - contradiction. }
 destruct i as [|i].
 { cbn [reference_immediate_refs reference_immediate_dependencies nth List.In].
 contradiction. }
 destruct i as [|i].
 { cbn [reference_immediate_refs reference_immediate_dependencies nth List.In].
 intro Member.
 destruct Member as [<-|Member].
 - right;exists 101%nat;vm_compute;repeat split;try reflexivity;lia.
 destruct Member as [<-|Member].
 - right;exists 61%nat;vm_compute;repeat split;try reflexivity;lia.
 - contradiction. }
 destruct i as [|i].
 { cbn [reference_immediate_refs reference_immediate_dependencies nth List.In].
 contradiction. }
 destruct i as [|i].
 { cbn [reference_immediate_refs reference_immediate_dependencies nth List.In].
 intro Member.
 destruct Member as [<-|Member].
 - right;exists 103%nat;vm_compute;repeat split;try reflexivity;lia.
 destruct Member as [<-|Member].
 - right;exists 61%nat;vm_compute;repeat split;try reflexivity;lia.
 - contradiction. }
 destruct i as [|i].
 { cbn [reference_immediate_refs reference_immediate_dependencies nth List.In].
 contradiction. }
 destruct i as [|i].
 { cbn [reference_immediate_refs reference_immediate_dependencies nth List.In].
 intro Member.
 destruct Member as [<-|Member].
 - right;exists 105%nat;vm_compute;repeat split;try reflexivity;lia.
 destruct Member as [<-|Member].
 - right;exists 61%nat;vm_compute;repeat split;try reflexivity;lia.
 - contradiction. }
 destruct i as [|i].
 { cbn [reference_immediate_refs reference_immediate_dependencies nth List.In].
 contradiction. }
 destruct i as [|i].
 { cbn [reference_immediate_refs reference_immediate_dependencies nth List.In].
 intro Member.
 destruct Member as [<-|Member].
 - right;exists 107%nat;vm_compute;repeat split;try reflexivity;lia.
 destruct Member as [<-|Member].
 - right;exists 61%nat;vm_compute;repeat split;try reflexivity;lia.
 - contradiction. }
 destruct i as [|i].
 { cbn [reference_immediate_refs reference_immediate_dependencies nth List.In].
 intro Member.
 destruct Member as [<-|Member].
 - left;reflexivity.
 - contradiction. }
 destruct i as [|i].
 { cbn [reference_immediate_refs reference_immediate_dependencies nth List.In].
 intro Member.
 destruct Member as [<-|Member].
 - left;reflexivity.
 - contradiction. }
 destruct i as [|i].
 { cbn [reference_immediate_refs reference_immediate_dependencies nth List.In].
 intro Member.
 destruct Member as [<-|Member].
 - left;reflexivity.
 - contradiction. }
 destruct i as [|i].
 { cbn [reference_immediate_refs reference_immediate_dependencies nth List.In].
 intro Member.
 destruct Member as [<-|Member].
 - left;reflexivity.
 - contradiction. }
 destruct i as [|i].
 { cbn [reference_immediate_refs reference_immediate_dependencies nth List.In].
 intro Member.
 destruct Member as [<-|Member].
 - left;reflexivity.
 - contradiction. }
 destruct i as [|i].
 { cbn [reference_immediate_refs reference_immediate_dependencies nth List.In].
 intro Member.
 destruct Member as [<-|Member].
 - left;reflexivity.
 - contradiction. }
 destruct i as [|i].
 { cbn [reference_immediate_refs reference_immediate_dependencies nth List.In].
 intro Member.
 destruct Member as [<-|Member].
 - right;exists 114%nat;vm_compute;repeat split;try reflexivity;lia.
 - contradiction. }
 destruct i as [|i].
 { cbn [reference_immediate_refs reference_immediate_dependencies nth List.In].
 intro Member.
 destruct Member as [<-|Member].
 - right;exists 113%nat;vm_compute;repeat split;try reflexivity;lia.
 destruct Member as [<-|Member].
 - right;exists 115%nat;vm_compute;repeat split;try reflexivity;lia.
 - contradiction. }
 destruct i as [|i].
 { cbn [reference_immediate_refs reference_immediate_dependencies nth List.In].
 intro Member.
 destruct Member as [<-|Member].
 - right;exists 112%nat;vm_compute;repeat split;try reflexivity;lia.
 destruct Member as [<-|Member].
 - right;exists 116%nat;vm_compute;repeat split;try reflexivity;lia.
 - contradiction. }
 destruct i as [|i].
 { cbn [reference_immediate_refs reference_immediate_dependencies nth List.In].
 intro Member.
 destruct Member as [<-|Member].
 - right;exists 111%nat;vm_compute;repeat split;try reflexivity;lia.
 destruct Member as [<-|Member].
 - right;exists 117%nat;vm_compute;repeat split;try reflexivity;lia.
 - contradiction. }
 destruct i as [|i].
 { cbn [reference_immediate_refs reference_immediate_dependencies nth List.In].
 intro Member.
 destruct Member as [<-|Member].
 - right;exists 110%nat;vm_compute;repeat split;try reflexivity;lia.
 destruct Member as [<-|Member].
 - right;exists 118%nat;vm_compute;repeat split;try reflexivity;lia.
 - contradiction. }
 destruct i as [|i].
 { cbn [reference_immediate_refs reference_immediate_dependencies nth List.In].
 intro Member.
 destruct Member as [<-|Member].
 - right;exists 109%nat;vm_compute;repeat split;try reflexivity;lia.
 destruct Member as [<-|Member].
 - right;exists 119%nat;vm_compute;repeat split;try reflexivity;lia.
 - contradiction. }
 destruct i as [|i].
 { cbn [reference_immediate_refs reference_immediate_dependencies nth List.In].
 intro Member.
 destruct Member as [<-|Member].
 - right;exists 120%nat;vm_compute;repeat split;try reflexivity;lia.
 - contradiction. }
 destruct i as [|i].
 { cbn [reference_immediate_refs reference_immediate_dependencies nth List.In].
 intro Member.
 destruct Member as [<-|Member].
 - right;exists 121%nat;vm_compute;repeat split;try reflexivity;lia.
 - contradiction. }
 destruct i as [|i].
 { cbn [reference_immediate_refs reference_immediate_dependencies nth List.In].
 intro Member.
 destruct Member as [<-|Member].
 - right;exists 8%nat;vm_compute;repeat split;try reflexivity;lia.
 - contradiction. }
 destruct i as [|i].
 { cbn [reference_immediate_refs reference_immediate_dependencies nth List.In].
 intro Member.
 destruct Member as [<-|Member].
 - right;exists 123%nat;vm_compute;repeat split;try reflexivity;lia.
 - contradiction. }
 destruct i as [|i].
 { cbn [reference_immediate_refs reference_immediate_dependencies nth List.In].
 intro Member.
 destruct Member as [<-|Member].
 - right;exists 124%nat;vm_compute;repeat split;try reflexivity;lia.
 - contradiction. }
 destruct i as [|i].
 { cbn [reference_immediate_refs reference_immediate_dependencies nth List.In].
 intro Member.
 destruct Member as [<-|Member].
 - right;exists 125%nat;vm_compute;repeat split;try reflexivity;lia.
 - contradiction. }
 destruct i as [|i].
 { cbn [reference_immediate_refs reference_immediate_dependencies nth List.In].
 intro Member.
 destruct Member as [<-|Member].
 - right;exists 11%nat;vm_compute;repeat split;try reflexivity;lia.
 - contradiction. }
 destruct i as [|i].
 { cbn [reference_immediate_refs reference_immediate_dependencies nth List.In].
 intro Member.
 destruct Member as [<-|Member].
 - right;exists 127%nat;vm_compute;repeat split;try reflexivity;lia.
 - contradiction. }
 destruct i as [|i].
 { cbn [reference_immediate_refs reference_immediate_dependencies nth List.In].
 intro Member.
 destruct Member as [<-|Member].
 - right;exists 128%nat;vm_compute;repeat split;try reflexivity;lia.
 - contradiction. }
 destruct i as [|i].
 { cbn [reference_immediate_refs reference_immediate_dependencies nth List.In].
 intro Member.
 destruct Member as [<-|Member].
 - right;exists 129%nat;vm_compute;repeat split;try reflexivity;lia.
 - contradiction. }
 destruct i as [|i].
 { cbn [reference_immediate_refs reference_immediate_dependencies nth List.In].
 intro Member.
 destruct Member as [<-|Member].
 - right;exists 14%nat;vm_compute;repeat split;try reflexivity;lia.
 - contradiction. }
 destruct i as [|i].
 { cbn [reference_immediate_refs reference_immediate_dependencies nth List.In].
 intro Member.
 destruct Member as [<-|Member].
 - right;exists 131%nat;vm_compute;repeat split;try reflexivity;lia.
 - contradiction. }
 destruct i as [|i].
 { cbn [reference_immediate_refs reference_immediate_dependencies nth List.In].
 intro Member.
 destruct Member as [<-|Member].
 - right;exists 132%nat;vm_compute;repeat split;try reflexivity;lia.
 - contradiction. }
 destruct i as [|i].
 { cbn [reference_immediate_refs reference_immediate_dependencies nth List.In].
 intro Member.
 destruct Member as [<-|Member].
 - right;exists 133%nat;vm_compute;repeat split;try reflexivity;lia.
 - contradiction. }
 destruct i as [|i].
 { cbn [reference_immediate_refs reference_immediate_dependencies nth List.In].
 intro Member.
 destruct Member as [<-|Member].
 - right;exists 17%nat;vm_compute;repeat split;try reflexivity;lia.
 - contradiction. }
 destruct i as [|i].
 { cbn [reference_immediate_refs reference_immediate_dependencies nth List.In].
 intro Member.
 destruct Member as [<-|Member].
 - right;exists 135%nat;vm_compute;repeat split;try reflexivity;lia.
 - contradiction. }
 destruct i as [|i].
 { cbn [reference_immediate_refs reference_immediate_dependencies nth List.In].
 intro Member.
 destruct Member as [<-|Member].
 - right;exists 136%nat;vm_compute;repeat split;try reflexivity;lia.
 - contradiction. }
 destruct i as [|i].
 { cbn [reference_immediate_refs reference_immediate_dependencies nth List.In].
 intro Member.
 destruct Member as [<-|Member].
 - right;exists 137%nat;vm_compute;repeat split;try reflexivity;lia.
 - contradiction. }
 destruct i as [|i].
 { cbn [reference_immediate_refs reference_immediate_dependencies nth List.In].
 intro Member.
 destruct Member as [<-|Member].
 - right;exists 20%nat;vm_compute;repeat split;try reflexivity;lia.
 - contradiction. }
 destruct i as [|i].
 { cbn [reference_immediate_refs reference_immediate_dependencies nth List.In].
 intro Member.
 destruct Member as [<-|Member].
 - right;exists 139%nat;vm_compute;repeat split;try reflexivity;lia.
 - contradiction. }
 destruct i as [|i].
 { cbn [reference_immediate_refs reference_immediate_dependencies nth List.In].
 intro Member.
 destruct Member as [<-|Member].
 - right;exists 140%nat;vm_compute;repeat split;try reflexivity;lia.
 - contradiction. }
 destruct i as [|i].
 { cbn [reference_immediate_refs reference_immediate_dependencies nth List.In].
 intro Member.
 destruct Member as [<-|Member].
 - right;exists 141%nat;vm_compute;repeat split;try reflexivity;lia.
 - contradiction. }
 destruct i as [|i].
 { cbn [reference_immediate_refs reference_immediate_dependencies nth List.In].
 intro Member.
 destruct Member as [<-|Member].
 - right;exists 23%nat;vm_compute;repeat split;try reflexivity;lia.
 - contradiction. }
 destruct i as [|i].
 { cbn [reference_immediate_refs reference_immediate_dependencies nth List.In].
 intro Member.
 destruct Member as [<-|Member].
 - right;exists 143%nat;vm_compute;repeat split;try reflexivity;lia.
 - contradiction. }
 destruct i as [|i].
 { cbn [reference_immediate_refs reference_immediate_dependencies nth List.In].
 intro Member.
 destruct Member as [<-|Member].
 - right;exists 144%nat;vm_compute;repeat split;try reflexivity;lia.
 - contradiction. }
 destruct i as [|i].
 { cbn [reference_immediate_refs reference_immediate_dependencies nth List.In].
 intro Member.
 destruct Member as [<-|Member].
 - right;exists 145%nat;vm_compute;repeat split;try reflexivity;lia.
 - contradiction. }
 destruct i as [|i].
 { cbn [reference_immediate_refs reference_immediate_dependencies nth List.In].
 intro Member.
 destruct Member as [<-|Member].
 - left;reflexivity.
 - contradiction. }
 destruct i as [|i].
 { cbn [reference_immediate_refs reference_immediate_dependencies nth List.In].
 intro Member.
 destruct Member as [<-|Member].
 - right;exists 147%nat;vm_compute;repeat split;try reflexivity;lia.
 - contradiction. }
 destruct i as [|i].
 { cbn [reference_immediate_refs reference_immediate_dependencies nth List.In].
 intro Member.
 destruct Member as [<-|Member].
 - right;exists 148%nat;vm_compute;repeat split;try reflexivity;lia.
 - contradiction. }
 destruct i as [|i].
 { cbn [reference_immediate_refs reference_immediate_dependencies nth List.In].
 intro Member.
 destruct Member as [<-|Member].
 - right;exists 149%nat;vm_compute;repeat split;try reflexivity;lia.
 - contradiction. }
 destruct i as [|i].
 { cbn [reference_immediate_refs reference_immediate_dependencies nth List.In].
 intro Member.
 destruct Member as [<-|Member].
 - right;exists 146%nat;vm_compute;repeat split;try reflexivity;lia.
 destruct Member as [<-|Member].
 - right;exists 150%nat;vm_compute;repeat split;try reflexivity;lia.
 - contradiction. }
 destruct i as [|i].
 { cbn [reference_immediate_refs reference_immediate_dependencies nth List.In].
 intro Member.
 destruct Member as [<-|Member].
 - right;exists 142%nat;vm_compute;repeat split;try reflexivity;lia.
 destruct Member as [<-|Member].
 - right;exists 151%nat;vm_compute;repeat split;try reflexivity;lia.
 - contradiction. }
 destruct i as [|i].
 { cbn [reference_immediate_refs reference_immediate_dependencies nth List.In].
 intro Member.
 destruct Member as [<-|Member].
 - right;exists 138%nat;vm_compute;repeat split;try reflexivity;lia.
 destruct Member as [<-|Member].
 - right;exists 152%nat;vm_compute;repeat split;try reflexivity;lia.
 - contradiction. }
 destruct i as [|i].
 { cbn [reference_immediate_refs reference_immediate_dependencies nth List.In].
 intro Member.
 destruct Member as [<-|Member].
 - right;exists 134%nat;vm_compute;repeat split;try reflexivity;lia.
 destruct Member as [<-|Member].
 - right;exists 153%nat;vm_compute;repeat split;try reflexivity;lia.
 - contradiction. }
 destruct i as [|i].
 { cbn [reference_immediate_refs reference_immediate_dependencies nth List.In].
 intro Member.
 destruct Member as [<-|Member].
 - right;exists 130%nat;vm_compute;repeat split;try reflexivity;lia.
 destruct Member as [<-|Member].
 - right;exists 154%nat;vm_compute;repeat split;try reflexivity;lia.
 - contradiction. }
 destruct i as [|i].
 { cbn [reference_immediate_refs reference_immediate_dependencies nth List.In].
 intro Member.
 destruct Member as [<-|Member].
 - right;exists 126%nat;vm_compute;repeat split;try reflexivity;lia.
 destruct Member as [<-|Member].
 - right;exists 155%nat;vm_compute;repeat split;try reflexivity;lia.
 - contradiction. }
 destruct i as [|i].
 { cbn [reference_immediate_refs reference_immediate_dependencies nth List.In].
 intro Member.
 destruct Member as [<-|Member].
 - right;exists 156%nat;vm_compute;repeat split;try reflexivity;lia.
 - contradiction. }
 destruct i as [|i].
 { cbn [reference_immediate_refs reference_immediate_dependencies nth List.In].
 intro Member.
 destruct Member as [<-|Member].
 - right;exists 157%nat;vm_compute;repeat split;try reflexivity;lia.
 - contradiction. }
 destruct i as [|i].
 { cbn [reference_immediate_refs reference_immediate_dependencies nth List.In].
 intro Member.
 destruct Member as [<-|Member].
 - right;exists 122%nat;vm_compute;repeat split;try reflexivity;lia.
 destruct Member as [<-|Member].
 - right;exists 158%nat;vm_compute;repeat split;try reflexivity;lia.
 - contradiction. }
 destruct i as [|i].
 { cbn [reference_immediate_refs reference_immediate_dependencies nth List.In].
 intro Member.
 destruct Member as [<-|Member].
 - right;exists 6%nat;vm_compute;repeat split;try reflexivity;lia.
 - contradiction. }
 destruct i as [|i].
 { cbn [reference_immediate_refs reference_immediate_dependencies nth List.In].
 intro Member.
 destruct Member as [<-|Member].
 - right;exists 9%nat;vm_compute;repeat split;try reflexivity;lia.
 - contradiction. }
 destruct i as [|i].
 { cbn [reference_immediate_refs reference_immediate_dependencies nth List.In].
 intro Member.
 destruct Member as [<-|Member].
 - right;exists 12%nat;vm_compute;repeat split;try reflexivity;lia.
 - contradiction. }
 destruct i as [|i].
 { cbn [reference_immediate_refs reference_immediate_dependencies nth List.In].
 intro Member.
 destruct Member as [<-|Member].
 - right;exists 15%nat;vm_compute;repeat split;try reflexivity;lia.
 - contradiction. }
 destruct i as [|i].
 { cbn [reference_immediate_refs reference_immediate_dependencies nth List.In].
 intro Member.
 destruct Member as [<-|Member].
 - right;exists 18%nat;vm_compute;repeat split;try reflexivity;lia.
 - contradiction. }
 destruct i as [|i].
 { cbn [reference_immediate_refs reference_immediate_dependencies nth List.In].
 intro Member.
 destruct Member as [<-|Member].
 - right;exists 21%nat;vm_compute;repeat split;try reflexivity;lia.
 - contradiction. }
 destruct i as [|i].
 { cbn [reference_immediate_refs reference_immediate_dependencies nth List.In].
 intro Member.
 destruct Member as [<-|Member].
 - right;exists 165%nat;vm_compute;repeat split;try reflexivity;lia.
 - contradiction. }
 destruct i as [|i].
 { cbn [reference_immediate_refs reference_immediate_dependencies nth List.In].
 intro Member.
 destruct Member as [<-|Member].
 - right;exists 164%nat;vm_compute;repeat split;try reflexivity;lia.
 destruct Member as [<-|Member].
 - right;exists 166%nat;vm_compute;repeat split;try reflexivity;lia.
 - contradiction. }
 destruct i as [|i].
 { cbn [reference_immediate_refs reference_immediate_dependencies nth List.In].
 intro Member.
 destruct Member as [<-|Member].
 - right;exists 163%nat;vm_compute;repeat split;try reflexivity;lia.
 destruct Member as [<-|Member].
 - right;exists 167%nat;vm_compute;repeat split;try reflexivity;lia.
 - contradiction. }
 destruct i as [|i].
 { cbn [reference_immediate_refs reference_immediate_dependencies nth List.In].
 intro Member.
 destruct Member as [<-|Member].
 - right;exists 162%nat;vm_compute;repeat split;try reflexivity;lia.
 destruct Member as [<-|Member].
 - right;exists 168%nat;vm_compute;repeat split;try reflexivity;lia.
 - contradiction. }
 destruct i as [|i].
 { cbn [reference_immediate_refs reference_immediate_dependencies nth List.In].
 intro Member.
 destruct Member as [<-|Member].
 - right;exists 161%nat;vm_compute;repeat split;try reflexivity;lia.
 destruct Member as [<-|Member].
 - right;exists 169%nat;vm_compute;repeat split;try reflexivity;lia.
 - contradiction. }
 destruct i as [|i].
 { cbn [reference_immediate_refs reference_immediate_dependencies nth List.In].
 intro Member.
 destruct Member as [<-|Member].
 - right;exists 160%nat;vm_compute;repeat split;try reflexivity;lia.
 destruct Member as [<-|Member].
 - right;exists 170%nat;vm_compute;repeat split;try reflexivity;lia.
 - contradiction. }
 destruct i as [|i].
 { cbn [reference_immediate_refs reference_immediate_dependencies nth List.In].
 intro Member.
 destruct Member as [<-|Member].
 - right;exists 171%nat;vm_compute;repeat split;try reflexivity;lia.
 - contradiction. }
 destruct i as [|i].
 { cbn [reference_immediate_refs reference_immediate_dependencies nth List.In].
 intro Member.
 destruct Member as [<-|Member].
 - right;exists 172%nat;vm_compute;repeat split;try reflexivity;lia.
 - contradiction. }
 destruct i as [|i].
 { cbn [reference_immediate_refs reference_immediate_dependencies nth List.In].
 intro Member.
 destruct Member as [<-|Member].
 - right;exists 159%nat;vm_compute;repeat split;try reflexivity;lia.
 destruct Member as [<-|Member].
 - right;exists 173%nat;vm_compute;repeat split;try reflexivity;lia.
 - contradiction. }
 destruct i as [|i].
 { cbn [reference_immediate_refs reference_immediate_dependencies nth List.In].
 intro Member.
 destruct Member as [<-|Member].
 - right;exists 124%nat;vm_compute;repeat split;try reflexivity;lia.
 - contradiction. }
 destruct i as [|i].
 { cbn [reference_immediate_refs reference_immediate_dependencies nth List.In].
 intro Member.
 destruct Member as [<-|Member].
 - right;exists 128%nat;vm_compute;repeat split;try reflexivity;lia.
 - contradiction. }
 destruct i as [|i].
 { cbn [reference_immediate_refs reference_immediate_dependencies nth List.In].
 intro Member.
 destruct Member as [<-|Member].
 - right;exists 132%nat;vm_compute;repeat split;try reflexivity;lia.
 - contradiction. }
 destruct i as [|i].
 { cbn [reference_immediate_refs reference_immediate_dependencies nth List.In].
 intro Member.
 destruct Member as [<-|Member].
 - right;exists 136%nat;vm_compute;repeat split;try reflexivity;lia.
 - contradiction. }
 destruct i as [|i].
 { cbn [reference_immediate_refs reference_immediate_dependencies nth List.In].
 intro Member.
 destruct Member as [<-|Member].
 - right;exists 140%nat;vm_compute;repeat split;try reflexivity;lia.
 - contradiction. }
 destruct i as [|i].
 { cbn [reference_immediate_refs reference_immediate_dependencies nth List.In].
 intro Member.
 destruct Member as [<-|Member].
 - right;exists 144%nat;vm_compute;repeat split;try reflexivity;lia.
 - contradiction. }
 destruct i as [|i].
 { cbn [reference_immediate_refs reference_immediate_dependencies nth List.In].
 intro Member.
 destruct Member as [<-|Member].
 - right;exists 180%nat;vm_compute;repeat split;try reflexivity;lia.
 - contradiction. }
 destruct i as [|i].
 { cbn [reference_immediate_refs reference_immediate_dependencies nth List.In].
 intro Member.
 destruct Member as [<-|Member].
 - right;exists 179%nat;vm_compute;repeat split;try reflexivity;lia.
 destruct Member as [<-|Member].
 - right;exists 181%nat;vm_compute;repeat split;try reflexivity;lia.
 - contradiction. }
 destruct i as [|i].
 { cbn [reference_immediate_refs reference_immediate_dependencies nth List.In].
 intro Member.
 destruct Member as [<-|Member].
 - right;exists 178%nat;vm_compute;repeat split;try reflexivity;lia.
 destruct Member as [<-|Member].
 - right;exists 182%nat;vm_compute;repeat split;try reflexivity;lia.
 - contradiction. }
 destruct i as [|i].
 { cbn [reference_immediate_refs reference_immediate_dependencies nth List.In].
 intro Member.
 destruct Member as [<-|Member].
 - right;exists 177%nat;vm_compute;repeat split;try reflexivity;lia.
 destruct Member as [<-|Member].
 - right;exists 183%nat;vm_compute;repeat split;try reflexivity;lia.
 - contradiction. }
 destruct i as [|i].
 { cbn [reference_immediate_refs reference_immediate_dependencies nth List.In].
 intro Member.
 destruct Member as [<-|Member].
 - right;exists 176%nat;vm_compute;repeat split;try reflexivity;lia.
 destruct Member as [<-|Member].
 - right;exists 184%nat;vm_compute;repeat split;try reflexivity;lia.
 - contradiction. }
 destruct i as [|i].
 { cbn [reference_immediate_refs reference_immediate_dependencies nth List.In].
 intro Member.
 destruct Member as [<-|Member].
 - right;exists 175%nat;vm_compute;repeat split;try reflexivity;lia.
 destruct Member as [<-|Member].
 - right;exists 185%nat;vm_compute;repeat split;try reflexivity;lia.
 - contradiction. }
 destruct i as [|i].
 { cbn [reference_immediate_refs reference_immediate_dependencies nth List.In].
 intro Member.
 destruct Member as [<-|Member].
 - right;exists 186%nat;vm_compute;repeat split;try reflexivity;lia.
 - contradiction. }
 destruct i as [|i].
 { cbn [reference_immediate_refs reference_immediate_dependencies nth List.In].
 intro Member.
 destruct Member as [<-|Member].
 - right;exists 187%nat;vm_compute;repeat split;try reflexivity;lia.
 - contradiction. }
 destruct i as [|i].
 { cbn [reference_immediate_refs reference_immediate_dependencies nth List.In].
 intro Member.
 destruct Member as [<-|Member].
 - right;exists 188%nat;vm_compute;repeat split;try reflexivity;lia.
 - contradiction. }
 destruct i as [|i].
 { cbn [reference_immediate_refs reference_immediate_dependencies nth List.In].
 intro Member.
 destruct Member as [<-|Member].
 - right;exists 174%nat;vm_compute;repeat split;try reflexivity;lia.
 destruct Member as [<-|Member].
 - right;exists 189%nat;vm_compute;repeat split;try reflexivity;lia.
 - contradiction. }
 destruct i as [|i].
 { cbn [reference_immediate_refs reference_immediate_dependencies nth List.In].
 contradiction. }
 destruct i as [|i].
 { cbn [reference_immediate_refs reference_immediate_dependencies nth List.In].
 intro Member.
 destruct Member as [<-|Member].
 - right;exists 191%nat;vm_compute;repeat split;try reflexivity;lia.
 destruct Member as [<-|Member].
 - right;exists 190%nat;vm_compute;repeat split;try reflexivity;lia.
 - contradiction. }
 destruct i as [|i].
 { cbn [reference_immediate_refs reference_immediate_dependencies nth List.In].
 intro Member.
 destruct Member as [<-|Member].
 - right;exists 122%nat;vm_compute;repeat split;try reflexivity;lia.
 destruct Member as [<-|Member].
 - right;exists 158%nat;vm_compute;repeat split;try reflexivity;lia.
 - contradiction. }
 destruct i as [|i].
 { cbn [reference_immediate_refs reference_immediate_dependencies nth List.In].
 intro Member.
 destruct Member as [<-|Member].
 - right;exists 193%nat;vm_compute;repeat split;try reflexivity;lia.
 destruct Member as [<-|Member].
 - right;exists 173%nat;vm_compute;repeat split;try reflexivity;lia.
 - contradiction. }
 destruct i as [|i].
 { cbn [reference_immediate_refs reference_immediate_dependencies nth List.In].
 intro Member.
 destruct Member as [<-|Member].
 - right;exists 188%nat;vm_compute;repeat split;try reflexivity;lia.
 - contradiction. }
 destruct i as [|i].
 { cbn [reference_immediate_refs reference_immediate_dependencies nth List.In].
 intro Member.
 destruct Member as [<-|Member].
 - right;exists 194%nat;vm_compute;repeat split;try reflexivity;lia.
 destruct Member as [<-|Member].
 - right;exists 195%nat;vm_compute;repeat split;try reflexivity;lia.
 - contradiction. }
 destruct i as [|i].
 { cbn [reference_immediate_refs reference_immediate_dependencies nth List.In].
 contradiction. }
 destruct i as [|i].
 { cbn [reference_immediate_refs reference_immediate_dependencies nth List.In].
 intro Member.
 destruct Member as [<-|Member].
 - right;exists 197%nat;vm_compute;repeat split;try reflexivity;lia.
 destruct Member as [<-|Member].
 - right;exists 196%nat;vm_compute;repeat split;try reflexivity;lia.
 - contradiction. }
 destruct i as [|i].
 { cbn [reference_immediate_refs reference_immediate_dependencies nth List.In].
 intro Member.
 destruct Member as [<-|Member].
 - right;exists 122%nat;vm_compute;repeat split;try reflexivity;lia.
 destruct Member as [<-|Member].
 - right;exists 158%nat;vm_compute;repeat split;try reflexivity;lia.
 - contradiction. }
 destruct i as [|i].
 { cbn [reference_immediate_refs reference_immediate_dependencies nth List.In].
 intro Member.
 destruct Member as [<-|Member].
 - right;exists 199%nat;vm_compute;repeat split;try reflexivity;lia.
 destruct Member as [<-|Member].
 - right;exists 173%nat;vm_compute;repeat split;try reflexivity;lia.
 - contradiction. }
 destruct i as [|i].
 { cbn [reference_immediate_refs reference_immediate_dependencies nth List.In].
 intro Member.
 destruct Member as [<-|Member].
 - right;exists 188%nat;vm_compute;repeat split;try reflexivity;lia.
 - contradiction. }
 destruct i as [|i].
 { cbn [reference_immediate_refs reference_immediate_dependencies nth List.In].
 intro Member.
 destruct Member as [<-|Member].
 - right;exists 200%nat;vm_compute;repeat split;try reflexivity;lia.
 destruct Member as [<-|Member].
 - right;exists 201%nat;vm_compute;repeat split;try reflexivity;lia.
 - contradiction. }
 destruct i as [|i].
 { cbn [reference_immediate_refs reference_immediate_dependencies nth List.In].
 contradiction. }
 destruct i as [|i].
 { cbn [reference_immediate_refs reference_immediate_dependencies nth List.In].
 intro Member.
 destruct Member as [<-|Member].
 - right;exists 203%nat;vm_compute;repeat split;try reflexivity;lia.
 destruct Member as [<-|Member].
 - right;exists 202%nat;vm_compute;repeat split;try reflexivity;lia.
 - contradiction. }
 destruct i as [|i].
 { cbn [reference_immediate_refs reference_immediate_dependencies nth List.In].
 intro Member.
 destruct Member as [<-|Member].
 - right;exists 122%nat;vm_compute;repeat split;try reflexivity;lia.
 destruct Member as [<-|Member].
 - right;exists 158%nat;vm_compute;repeat split;try reflexivity;lia.
 - contradiction. }
 destruct i as [|i].
 { cbn [reference_immediate_refs reference_immediate_dependencies nth List.In].
 intro Member.
 destruct Member as [<-|Member].
 - right;exists 205%nat;vm_compute;repeat split;try reflexivity;lia.
 destruct Member as [<-|Member].
 - right;exists 173%nat;vm_compute;repeat split;try reflexivity;lia.
 - contradiction. }
 destruct i as [|i].
 { cbn [reference_immediate_refs reference_immediate_dependencies nth List.In].
 intro Member.
 destruct Member as [<-|Member].
 - right;exists 188%nat;vm_compute;repeat split;try reflexivity;lia.
 - contradiction. }
 destruct i as [|i].
 { cbn [reference_immediate_refs reference_immediate_dependencies nth List.In].
 intro Member.
 destruct Member as [<-|Member].
 - right;exists 206%nat;vm_compute;repeat split;try reflexivity;lia.
 destruct Member as [<-|Member].
 - right;exists 207%nat;vm_compute;repeat split;try reflexivity;lia.
 - contradiction. }
 destruct i as [|i].
 { cbn [reference_immediate_refs reference_immediate_dependencies nth List.In].
 contradiction. }
 destruct i as [|i].
 { cbn [reference_immediate_refs reference_immediate_dependencies nth List.In].
 intro Member.
 destruct Member as [<-|Member].
 - right;exists 209%nat;vm_compute;repeat split;try reflexivity;lia.
 destruct Member as [<-|Member].
 - right;exists 208%nat;vm_compute;repeat split;try reflexivity;lia.
 - contradiction. }
 destruct i as [|i].
 { cbn [reference_immediate_refs reference_immediate_dependencies nth List.In].
 intro Member.
 destruct Member as [<-|Member].
 - right;exists 122%nat;vm_compute;repeat split;try reflexivity;lia.
 destruct Member as [<-|Member].
 - right;exists 158%nat;vm_compute;repeat split;try reflexivity;lia.
 - contradiction. }
 destruct i as [|i].
 { cbn [reference_immediate_refs reference_immediate_dependencies nth List.In].
 intro Member.
 destruct Member as [<-|Member].
 - right;exists 211%nat;vm_compute;repeat split;try reflexivity;lia.
 destruct Member as [<-|Member].
 - right;exists 173%nat;vm_compute;repeat split;try reflexivity;lia.
 - contradiction. }
 destruct i as [|i].
 { cbn [reference_immediate_refs reference_immediate_dependencies nth List.In].
 intro Member.
 destruct Member as [<-|Member].
 - right;exists 188%nat;vm_compute;repeat split;try reflexivity;lia.
 - contradiction. }
 destruct i as [|i].
 { cbn [reference_immediate_refs reference_immediate_dependencies nth List.In].
 intro Member.
 destruct Member as [<-|Member].
 - right;exists 212%nat;vm_compute;repeat split;try reflexivity;lia.
 destruct Member as [<-|Member].
 - right;exists 213%nat;vm_compute;repeat split;try reflexivity;lia.
 - contradiction. }
 destruct i as [|i].
 { cbn [reference_immediate_refs reference_immediate_dependencies nth List.In].
 contradiction. }
 destruct i as [|i].
 { cbn [reference_immediate_refs reference_immediate_dependencies nth List.In].
 intro Member.
 destruct Member as [<-|Member].
 - right;exists 215%nat;vm_compute;repeat split;try reflexivity;lia.
 destruct Member as [<-|Member].
 - right;exists 214%nat;vm_compute;repeat split;try reflexivity;lia.
 - contradiction. }
 destruct i as [|i].
 { cbn [reference_immediate_refs reference_immediate_dependencies nth List.In].
 intro Member.
 destruct Member as [<-|Member].
 - right;exists 122%nat;vm_compute;repeat split;try reflexivity;lia.
 destruct Member as [<-|Member].
 - right;exists 158%nat;vm_compute;repeat split;try reflexivity;lia.
 - contradiction. }
 destruct i as [|i].
 { cbn [reference_immediate_refs reference_immediate_dependencies nth List.In].
 intro Member.
 destruct Member as [<-|Member].
 - right;exists 217%nat;vm_compute;repeat split;try reflexivity;lia.
 destruct Member as [<-|Member].
 - right;exists 173%nat;vm_compute;repeat split;try reflexivity;lia.
 - contradiction. }
 destruct i as [|i].
 { cbn [reference_immediate_refs reference_immediate_dependencies nth List.In].
 intro Member.
 destruct Member as [<-|Member].
 - right;exists 188%nat;vm_compute;repeat split;try reflexivity;lia.
 - contradiction. }
 destruct i as [|i].
 { cbn [reference_immediate_refs reference_immediate_dependencies nth List.In].
 intro Member.
 destruct Member as [<-|Member].
 - right;exists 218%nat;vm_compute;repeat split;try reflexivity;lia.
 destruct Member as [<-|Member].
 - right;exists 219%nat;vm_compute;repeat split;try reflexivity;lia.
 - contradiction. }
 destruct i as [|i].
 { cbn [reference_immediate_refs reference_immediate_dependencies nth List.In].
 contradiction. }
 destruct i as [|i].
 { cbn [reference_immediate_refs reference_immediate_dependencies nth List.In].
 intro Member.
 destruct Member as [<-|Member].
 - right;exists 221%nat;vm_compute;repeat split;try reflexivity;lia.
 destruct Member as [<-|Member].
 - right;exists 220%nat;vm_compute;repeat split;try reflexivity;lia.
 - contradiction. }
 destruct i as [|i].
 { cbn [reference_immediate_refs reference_immediate_dependencies nth List.In].
 contradiction. }
 destruct i as [|i].
 { cbn [reference_immediate_refs reference_immediate_dependencies nth List.In].
 intro Member.
 destruct Member as [<-|Member].
 - right;exists 223%nat;vm_compute;repeat split;try reflexivity;lia.
 destruct Member as [<-|Member].
 - right;exists 61%nat;vm_compute;repeat split;try reflexivity;lia.
 - contradiction. }
 destruct i as [|i].
 { cbn [reference_immediate_refs reference_immediate_dependencies nth List.In].
 intro Member.
 destruct Member as [<-|Member].
 - left;reflexivity.
 - contradiction. }
 destruct i as [|i].
 { cbn [reference_immediate_refs reference_immediate_dependencies nth List.In].
 intro Member.
 destruct Member as [<-|Member].
 - right;exists 225%nat;vm_compute;repeat split;try reflexivity;lia.
 - contradiction. }
 destruct i as [|i].
 { cbn [reference_immediate_refs reference_immediate_dependencies nth List.In].
 intro Member.
 destruct Member as [<-|Member].
 - right;exists 226%nat;vm_compute;repeat split;try reflexivity;lia.
 - contradiction. }
 destruct i as [|i].
 { cbn [reference_immediate_refs reference_immediate_dependencies nth List.In].
 intro Member.
 destruct Member as [<-|Member].
 - right;exists 227%nat;vm_compute;repeat split;try reflexivity;lia.
 - contradiction. }
 destruct i as [|i].
 { cbn [reference_immediate_refs reference_immediate_dependencies nth List.In].
 intro Member.
 destruct Member as [<-|Member].
 - right;exists 148%nat;vm_compute;repeat split;try reflexivity;lia.
 - contradiction. }
 destruct i as [|i].
 { cbn [reference_immediate_refs reference_immediate_dependencies nth List.In].
 intro Member.
 destruct Member as [<-|Member].
 - right;exists 229%nat;vm_compute;repeat split;try reflexivity;lia.
 - contradiction. }
 destruct i as [|i].
 { cbn [reference_immediate_refs reference_immediate_dependencies nth List.In].
 intro Member.
 destruct Member as [<-|Member].
 - right;exists 230%nat;vm_compute;repeat split;try reflexivity;lia.
 - contradiction. }
 destruct i as [|i].
 { cbn [reference_immediate_refs reference_immediate_dependencies nth List.In].
 intro Member.
 destruct Member as [<-|Member].
 - right;exists 231%nat;vm_compute;repeat split;try reflexivity;lia.
 - contradiction. }
 destruct i as [|i].
 { cbn [reference_immediate_refs reference_immediate_dependencies nth List.In].
 intro Member.
 destruct Member as [<-|Member].
 - right;exists 232%nat;vm_compute;repeat split;try reflexivity;lia.
 - contradiction. }
 destruct i as [|i].
 { cbn [reference_immediate_refs reference_immediate_dependencies nth List.In].
 intro Member.
 destruct Member as [<-|Member].
 - right;exists 228%nat;vm_compute;repeat split;try reflexivity;lia.
 destruct Member as [<-|Member].
 - right;exists 233%nat;vm_compute;repeat split;try reflexivity;lia.
 - contradiction. }
 destruct i as [|i].
 { cbn [reference_immediate_refs reference_immediate_dependencies nth List.In].
 intro Member.
 destruct Member as [<-|Member].
 - right;exists 234%nat;vm_compute;repeat split;try reflexivity;lia.
 destruct Member as [<-|Member].
 - right;exists 158%nat;vm_compute;repeat split;try reflexivity;lia.
 - contradiction. }
 destruct i as [|i].
 { cbn [reference_immediate_refs reference_immediate_dependencies nth List.In].
 intro Member.
 destruct Member as [<-|Member].
 - right;exists 147%nat;vm_compute;repeat split;try reflexivity;lia.
 - contradiction. }
 destruct i as [|i].
 { cbn [reference_immediate_refs reference_immediate_dependencies nth List.In].
 intro Member.
 destruct Member as [<-|Member].
 - right;exists 236%nat;vm_compute;repeat split;try reflexivity;lia.
 - contradiction. }
 destruct i as [|i].
 { cbn [reference_immediate_refs reference_immediate_dependencies nth List.In].
 intro Member.
 destruct Member as [<-|Member].
 - right;exists 237%nat;vm_compute;repeat split;try reflexivity;lia.
 - contradiction. }
 destruct i as [|i].
 { cbn [reference_immediate_refs reference_immediate_dependencies nth List.In].
 intro Member.
 destruct Member as [<-|Member].
 - right;exists 238%nat;vm_compute;repeat split;try reflexivity;lia.
 - contradiction. }
 destruct i as [|i].
 { cbn [reference_immediate_refs reference_immediate_dependencies nth List.In].
 intro Member.
 destruct Member as [<-|Member].
 - right;exists 239%nat;vm_compute;repeat split;try reflexivity;lia.
 - contradiction. }
 destruct i as [|i].
 { cbn [reference_immediate_refs reference_immediate_dependencies nth List.In].
 intro Member.
 destruct Member as [<-|Member].
 - right;exists 235%nat;vm_compute;repeat split;try reflexivity;lia.
 destruct Member as [<-|Member].
 - right;exists 240%nat;vm_compute;repeat split;try reflexivity;lia.
 - contradiction. }
 destruct i as [|i].
 { cbn [reference_immediate_refs reference_immediate_dependencies nth List.In].
 contradiction. }
 destruct i as [|i].
 { cbn [reference_immediate_refs reference_immediate_dependencies nth List.In].
 intro Member.
 destruct Member as [<-|Member].
 - right;exists 242%nat;vm_compute;repeat split;try reflexivity;lia.
 destruct Member as [<-|Member].
 - right;exists 241%nat;vm_compute;repeat split;try reflexivity;lia.
 - contradiction. }
 destruct i as [|i].
 { cbn [reference_immediate_refs reference_immediate_dependencies nth List.In].
 intro Member.
 destruct Member as [<-|Member].
 - left;reflexivity.
 - contradiction. }
 destruct i as [|i].
 { cbn [reference_immediate_refs reference_immediate_dependencies nth List.In].
 intro Member.
 destruct Member as [<-|Member].
 - left;reflexivity.
 - contradiction. }
 destruct i as [|i].
 { cbn [reference_immediate_refs reference_immediate_dependencies nth List.In].
 intro Member.
 destruct Member as [<-|Member].
 - right;exists 245%nat;vm_compute;repeat split;try reflexivity;lia.
 - contradiction. }
 destruct i as [|i].
 { cbn [reference_immediate_refs reference_immediate_dependencies nth List.In].
 intro Member.
 destruct Member as [<-|Member].
 - right;exists 244%nat;vm_compute;repeat split;try reflexivity;lia.
 destruct Member as [<-|Member].
 - right;exists 246%nat;vm_compute;repeat split;try reflexivity;lia.
 - contradiction. }
 destruct i as [|i].
 { cbn [reference_immediate_refs reference_immediate_dependencies nth List.In].
 intro Member.
 destruct Member as [<-|Member].
 - right;exists 247%nat;vm_compute;repeat split;try reflexivity;lia.
 - contradiction. }
 destruct i as [|i].
 { cbn [reference_immediate_refs reference_immediate_dependencies nth List.In].
 intro Member.
 destruct Member as [<-|Member].
 - right;exists 248%nat;vm_compute;repeat split;try reflexivity;lia.
 - contradiction. }
 destruct i as [|i].
 { cbn [reference_immediate_refs reference_immediate_dependencies nth List.In].
 intro Member.
 destruct Member as [<-|Member].
 - right;exists 249%nat;vm_compute;repeat split;try reflexivity;lia.
 - contradiction. }
 destruct i as [|i].
 { cbn [reference_immediate_refs reference_immediate_dependencies nth List.In].
 intro Member.
 destruct Member as [<-|Member].
 - right;exists 250%nat;vm_compute;repeat split;try reflexivity;lia.
 - contradiction. }
 destruct i as [|i].
 { cbn [reference_immediate_refs reference_immediate_dependencies nth List.In].
 intro Member.
 destruct Member as [<-|Member].
 - right;exists 249%nat;vm_compute;repeat split;try reflexivity;lia.
 - contradiction. }
 destruct i as [|i].
 { cbn [reference_immediate_refs reference_immediate_dependencies nth List.In].
 intro Member.
 destruct Member as [<-|Member].
 - right;exists 252%nat;vm_compute;repeat split;try reflexivity;lia.
 - contradiction. }
 destruct i as [|i].
 { cbn [reference_immediate_refs reference_immediate_dependencies nth List.In].
 contradiction. }
 destruct i as [|i].
 { cbn [reference_immediate_refs reference_immediate_dependencies nth List.In].
 intro Member.
 destruct Member as [<-|Member].
 - right;exists 254%nat;vm_compute;repeat split;try reflexivity;lia.
 destruct Member as [<-|Member].
 - right;exists 61%nat;vm_compute;repeat split;try reflexivity;lia.
 - contradiction. }
 destruct i as [|i].
 { cbn [reference_immediate_refs reference_immediate_dependencies nth List.In].
 contradiction. }
 destruct i as [|i].
 { cbn [reference_immediate_refs reference_immediate_dependencies nth List.In].
 intro Member.
 destruct Member as [<-|Member].
 - right;exists 256%nat;vm_compute;repeat split;try reflexivity;lia.
 destruct Member as [<-|Member].
 - right;exists 61%nat;vm_compute;repeat split;try reflexivity;lia.
 - contradiction. }
 destruct i as [|i].
 { cbn [reference_immediate_refs reference_immediate_dependencies nth List.In].
 contradiction. }
 destruct i as [|i].
 { cbn [reference_immediate_refs reference_immediate_dependencies nth List.In].
 intro Member.
 destruct Member as [<-|Member].
 - right;exists 258%nat;vm_compute;repeat split;try reflexivity;lia.
 destruct Member as [<-|Member].
 - right;exists 61%nat;vm_compute;repeat split;try reflexivity;lia.
 - contradiction. }
 destruct i as [|i].
 { cbn [reference_immediate_refs reference_immediate_dependencies nth List.In].
 contradiction. }
 destruct i as [|i].
 { cbn [reference_immediate_refs reference_immediate_dependencies nth List.In].
 intro Member.
 destruct Member as [<-|Member].
 - right;exists 260%nat;vm_compute;repeat split;try reflexivity;lia.
 destruct Member as [<-|Member].
 - right;exists 61%nat;vm_compute;repeat split;try reflexivity;lia.
 - contradiction. }
 destruct i as [|i].
 { cbn [reference_immediate_refs reference_immediate_dependencies nth List.In].
 contradiction. }
 destruct i as [|i].
 { cbn [reference_immediate_refs reference_immediate_dependencies nth List.In].
 intro Member.
 destruct Member as [<-|Member].
 - right;exists 262%nat;vm_compute;repeat split;try reflexivity;lia.
 destruct Member as [<-|Member].
 - right;exists 61%nat;vm_compute;repeat split;try reflexivity;lia.
 - contradiction. }
 destruct i as [|i].
 { cbn [reference_immediate_refs reference_immediate_dependencies nth List.In].
 contradiction. }
 destruct i as [|i].
 { cbn [reference_immediate_refs reference_immediate_dependencies nth List.In].
 intro Member.
 destruct Member as [<-|Member].
 - right;exists 264%nat;vm_compute;repeat split;try reflexivity;lia.
 destruct Member as [<-|Member].
 - right;exists 61%nat;vm_compute;repeat split;try reflexivity;lia.
 - contradiction. }
 destruct i as [|i].
 { cbn [reference_immediate_refs reference_immediate_dependencies nth List.In].
 contradiction. }
 destruct i as [|i].
 { cbn [reference_immediate_refs reference_immediate_dependencies nth List.In].
 intro Member.
 destruct Member as [<-|Member].
 - right;exists 266%nat;vm_compute;repeat split;try reflexivity;lia.
 destruct Member as [<-|Member].
 - right;exists 61%nat;vm_compute;repeat split;try reflexivity;lia.
 - contradiction. }
 destruct i as [|i].
 { cbn [reference_immediate_refs reference_immediate_dependencies nth List.In].
 contradiction. }
 destruct i as [|i].
 { cbn [reference_immediate_refs reference_immediate_dependencies nth List.In].
 intro Member.
 destruct Member as [<-|Member].
 - right;exists 268%nat;vm_compute;repeat split;try reflexivity;lia.
 destruct Member as [<-|Member].
 - right;exists 61%nat;vm_compute;repeat split;try reflexivity;lia.
 - contradiction. }
 destruct i as [|i].
 { cbn [reference_immediate_refs reference_immediate_dependencies nth List.In].
 contradiction. }
 destruct i as [|i].
 { cbn [reference_immediate_refs reference_immediate_dependencies nth List.In].
 intro Member.
 destruct Member as [<-|Member].
 - right;exists 270%nat;vm_compute;repeat split;try reflexivity;lia.
 destruct Member as [<-|Member].
 - right;exists 61%nat;vm_compute;repeat split;try reflexivity;lia.
 - contradiction. }
 destruct i as [|i].
 { cbn [reference_immediate_refs reference_immediate_dependencies nth List.In].
 intro Member.
 destruct Member as [<-|Member].
 - right;exists 271%nat;vm_compute;repeat split;try reflexivity;lia.
 - contradiction. }
 destruct i as [|i].
 { cbn [reference_immediate_refs reference_immediate_dependencies nth List.In].
 intro Member.
 destruct Member as [<-|Member].
 - right;exists 269%nat;vm_compute;repeat split;try reflexivity;lia.
 destruct Member as [<-|Member].
 - right;exists 272%nat;vm_compute;repeat split;try reflexivity;lia.
 - contradiction. }
 destruct i as [|i].
 { cbn [reference_immediate_refs reference_immediate_dependencies nth List.In].
 intro Member.
 destruct Member as [<-|Member].
 - right;exists 267%nat;vm_compute;repeat split;try reflexivity;lia.
 destruct Member as [<-|Member].
 - right;exists 273%nat;vm_compute;repeat split;try reflexivity;lia.
 - contradiction. }
 destruct i as [|i].
 { cbn [reference_immediate_refs reference_immediate_dependencies nth List.In].
 intro Member.
 destruct Member as [<-|Member].
 - right;exists 265%nat;vm_compute;repeat split;try reflexivity;lia.
 destruct Member as [<-|Member].
 - right;exists 274%nat;vm_compute;repeat split;try reflexivity;lia.
 - contradiction. }
 destruct i as [|i].
 { cbn [reference_immediate_refs reference_immediate_dependencies nth List.In].
 intro Member.
 destruct Member as [<-|Member].
 - right;exists 263%nat;vm_compute;repeat split;try reflexivity;lia.
 destruct Member as [<-|Member].
 - right;exists 275%nat;vm_compute;repeat split;try reflexivity;lia.
 - contradiction. }
 destruct i as [|i].
 { cbn [reference_immediate_refs reference_immediate_dependencies nth List.In].
 intro Member.
 destruct Member as [<-|Member].
 - right;exists 261%nat;vm_compute;repeat split;try reflexivity;lia.
 destruct Member as [<-|Member].
 - right;exists 276%nat;vm_compute;repeat split;try reflexivity;lia.
 - contradiction. }
 destruct i as [|i].
 { cbn [reference_immediate_refs reference_immediate_dependencies nth List.In].
 intro Member.
 destruct Member as [<-|Member].
 - right;exists 259%nat;vm_compute;repeat split;try reflexivity;lia.
 destruct Member as [<-|Member].
 - right;exists 277%nat;vm_compute;repeat split;try reflexivity;lia.
 - contradiction. }
 destruct i as [|i].
 { cbn [reference_immediate_refs reference_immediate_dependencies nth List.In].
 intro Member.
 destruct Member as [<-|Member].
 - right;exists 257%nat;vm_compute;repeat split;try reflexivity;lia.
 destruct Member as [<-|Member].
 - right;exists 278%nat;vm_compute;repeat split;try reflexivity;lia.
 - contradiction. }
 destruct i as [|i].
 { cbn [reference_immediate_refs reference_immediate_dependencies nth List.In].
 intro Member.
 destruct Member as [<-|Member].
 - right;exists 255%nat;vm_compute;repeat split;try reflexivity;lia.
 destruct Member as [<-|Member].
 - right;exists 279%nat;vm_compute;repeat split;try reflexivity;lia.
 - contradiction. }
 destruct i as [|i].
 { cbn [reference_immediate_refs reference_immediate_dependencies nth List.In].
 intro Member.
 destruct Member as [<-|Member].
 - right;exists 253%nat;vm_compute;repeat split;try reflexivity;lia.
 destruct Member as [<-|Member].
 - right;exists 280%nat;vm_compute;repeat split;try reflexivity;lia.
 - contradiction. }
 destruct i as [|i].
 { cbn [reference_immediate_refs reference_immediate_dependencies nth List.In].
 intro Member.
 destruct Member as [<-|Member].
 - right;exists 251%nat;vm_compute;repeat split;try reflexivity;lia.
 destruct Member as [<-|Member].
 - right;exists 281%nat;vm_compute;repeat split;try reflexivity;lia.
 - contradiction. }
 destruct i as [|i].
 { cbn [reference_immediate_refs reference_immediate_dependencies nth List.In].
 intro Member.
 destruct Member as [<-|Member].
 - right;exists 243%nat;vm_compute;repeat split;try reflexivity;lia.
 destruct Member as [<-|Member].
 - right;exists 282%nat;vm_compute;repeat split;try reflexivity;lia.
 - contradiction. }
 destruct i as [|i].
 { cbn [reference_immediate_refs reference_immediate_dependencies nth List.In].
 intro Member.
 destruct Member as [<-|Member].
 - right;exists 224%nat;vm_compute;repeat split;try reflexivity;lia.
 destruct Member as [<-|Member].
 - right;exists 283%nat;vm_compute;repeat split;try reflexivity;lia.
 - contradiction. }
 destruct i as [|i].
 { cbn [reference_immediate_refs reference_immediate_dependencies nth List.In].
 intro Member.
 destruct Member as [<-|Member].
 - right;exists 222%nat;vm_compute;repeat split;try reflexivity;lia.
 destruct Member as [<-|Member].
 - right;exists 284%nat;vm_compute;repeat split;try reflexivity;lia.
 - contradiction. }
 destruct i as [|i].
 { cbn [reference_immediate_refs reference_immediate_dependencies nth List.In].
 intro Member.
 destruct Member as [<-|Member].
 - right;exists 216%nat;vm_compute;repeat split;try reflexivity;lia.
 destruct Member as [<-|Member].
 - right;exists 285%nat;vm_compute;repeat split;try reflexivity;lia.
 - contradiction. }
 destruct i as [|i].
 { cbn [reference_immediate_refs reference_immediate_dependencies nth List.In].
 intro Member.
 destruct Member as [<-|Member].
 - right;exists 210%nat;vm_compute;repeat split;try reflexivity;lia.
 destruct Member as [<-|Member].
 - right;exists 286%nat;vm_compute;repeat split;try reflexivity;lia.
 - contradiction. }
 destruct i as [|i].
 { cbn [reference_immediate_refs reference_immediate_dependencies nth List.In].
 intro Member.
 destruct Member as [<-|Member].
 - right;exists 204%nat;vm_compute;repeat split;try reflexivity;lia.
 destruct Member as [<-|Member].
 - right;exists 287%nat;vm_compute;repeat split;try reflexivity;lia.
 - contradiction. }
 destruct i as [|i].
 { cbn [reference_immediate_refs reference_immediate_dependencies nth List.In].
 intro Member.
 destruct Member as [<-|Member].
 - right;exists 198%nat;vm_compute;repeat split;try reflexivity;lia.
 destruct Member as [<-|Member].
 - right;exists 288%nat;vm_compute;repeat split;try reflexivity;lia.
 - contradiction. }
 destruct i as [|i].
 { cbn [reference_immediate_refs reference_immediate_dependencies nth List.In].
 intro Member.
 destruct Member as [<-|Member].
 - right;exists 192%nat;vm_compute;repeat split;try reflexivity;lia.
 destruct Member as [<-|Member].
 - right;exists 289%nat;vm_compute;repeat split;try reflexivity;lia.
 - contradiction. }
 destruct i as [|i].
 { cbn [reference_immediate_refs reference_immediate_dependencies nth List.In].
 intro Member.
 destruct Member as [<-|Member].
 - right;exists 108%nat;vm_compute;repeat split;try reflexivity;lia.
 destruct Member as [<-|Member].
 - right;exists 290%nat;vm_compute;repeat split;try reflexivity;lia.
 - contradiction. }
 destruct i as [|i].
 { cbn [reference_immediate_refs reference_immediate_dependencies nth List.In].
 intro Member.
 destruct Member as [<-|Member].
 - right;exists 106%nat;vm_compute;repeat split;try reflexivity;lia.
 destruct Member as [<-|Member].
 - right;exists 291%nat;vm_compute;repeat split;try reflexivity;lia.
 - contradiction. }
 destruct i as [|i].
 { cbn [reference_immediate_refs reference_immediate_dependencies nth List.In].
 intro Member.
 destruct Member as [<-|Member].
 - right;exists 104%nat;vm_compute;repeat split;try reflexivity;lia.
 destruct Member as [<-|Member].
 - right;exists 292%nat;vm_compute;repeat split;try reflexivity;lia.
 - contradiction. }
 destruct i as [|i].
 { cbn [reference_immediate_refs reference_immediate_dependencies nth List.In].
 intro Member.
 destruct Member as [<-|Member].
 - right;exists 102%nat;vm_compute;repeat split;try reflexivity;lia.
 destruct Member as [<-|Member].
 - right;exists 293%nat;vm_compute;repeat split;try reflexivity;lia.
 - contradiction. }
 destruct i as [|i].
 { cbn [reference_immediate_refs reference_immediate_dependencies nth List.In].
 intro Member.
 destruct Member as [<-|Member].
 - right;exists 100%nat;vm_compute;repeat split;try reflexivity;lia.
 destruct Member as [<-|Member].
 - right;exists 294%nat;vm_compute;repeat split;try reflexivity;lia.
 - contradiction. }
 destruct i as [|i].
 { cbn [reference_immediate_refs reference_immediate_dependencies nth List.In].
 intro Member.
 destruct Member as [<-|Member].
 - right;exists 98%nat;vm_compute;repeat split;try reflexivity;lia.
 destruct Member as [<-|Member].
 - right;exists 295%nat;vm_compute;repeat split;try reflexivity;lia.
 - contradiction. }
 destruct i as [|i].
 { cbn [reference_immediate_refs reference_immediate_dependencies nth List.In].
 intro Member.
 destruct Member as [<-|Member].
 - right;exists 95%nat;vm_compute;repeat split;try reflexivity;lia.
 destruct Member as [<-|Member].
 - right;exists 296%nat;vm_compute;repeat split;try reflexivity;lia.
 - contradiction. }
 destruct i as [|i].
 { cbn [reference_immediate_refs reference_immediate_dependencies nth List.In].
 intro Member.
 destruct Member as [<-|Member].
 - right;exists 92%nat;vm_compute;repeat split;try reflexivity;lia.
 destruct Member as [<-|Member].
 - right;exists 297%nat;vm_compute;repeat split;try reflexivity;lia.
 - contradiction. }
 destruct i as [|i].
 { cbn [reference_immediate_refs reference_immediate_dependencies nth List.In].
 intro Member.
 destruct Member as [<-|Member].
 - right;exists 67%nat;vm_compute;repeat split;try reflexivity;lia.
 destruct Member as [<-|Member].
 - right;exists 298%nat;vm_compute;repeat split;try reflexivity;lia.
 - contradiction. }
 destruct i as [|i].
 { cbn [reference_immediate_refs reference_immediate_dependencies nth List.In].
 intro Member.
 destruct Member as [<-|Member].
 - right;exists 65%nat;vm_compute;repeat split;try reflexivity;lia.
 destruct Member as [<-|Member].
 - right;exists 299%nat;vm_compute;repeat split;try reflexivity;lia.
 - contradiction. }
 destruct i as [|i].
 { cbn [reference_immediate_refs reference_immediate_dependencies nth List.In].
 intro Member.
 destruct Member as [<-|Member].
 - right;exists 63%nat;vm_compute;repeat split;try reflexivity;lia.
 destruct Member as [<-|Member].
 - right;exists 300%nat;vm_compute;repeat split;try reflexivity;lia.
 - contradiction. }
 destruct i as [|i].
 { cbn [reference_immediate_refs reference_immediate_dependencies nth List.In].
 intro Member.
 destruct Member as [<-|Member].
 - right;exists 301%nat;vm_compute;repeat split;try reflexivity;lia.
 - contradiction. }
 destruct i as [|i].
 { cbn [reference_immediate_refs reference_immediate_dependencies nth List.In].
 intro Member.
 destruct Member as [<-|Member].
 - right;exists 302%nat;vm_compute;repeat split;try reflexivity;lia.
 - contradiction. }
 lia.
Qed.
Theorem reference_immediate_node_type_step i invalid old result : (i < 304)%coq_nat ->
 (forall site value, eval_hfexpr_validif_policy (isolated_validif_policy invalid) site flat_memories (reference_immediate_expression i) old old = Some value -> type_of_val value = Gtyp (Fuint (reference_immediate_width i))) ->
 formal_value_iter invalid flat_memories old false old flat_statements = Some result ->
 exists value, VM.find (reference_immediate_node i) result = Some value /\ type_of_val value = Gtyp (Fuint (reference_immediate_width i)).
Proof.
 intros Bound Shape Step.
 assert (Position : select_node_offsets (reference_immediate_offsets i) flat_statements = Some (reference_immediate_nodes i)).
 { unfold reference_immediate_offsets,reference_immediate_nodes;destruct (nth 2%nat reference_immediate_groups i) as [|[|g]];[exact reference_control_0_positions|exact reference_control_1_positions|exact reference_control_2_positions]. }
 assert (Safety : selected_node_safety flat_memories flat_statements (reference_immediate_offsets i) flat_statements = true).
 { unfold reference_immediate_offsets;destruct (nth 2%nat reference_immediate_groups i) as [|[|g]];[exact reference_control_0_safety|exact reference_control_1_safety|exact reference_control_2_safety]. }
 destruct (selected_node_safe_position flat_memories flat_statements (reference_immediate_offsets i) flat_statements (reference_immediate_nodes i) _ _ Position Safety (reference_immediate_member i Bound)) as [count [tail [Pos [Safe Nonreg]]]].
 destruct (formal_successful_node_evaluation count flat_statements tail _ _ invalid flat_memories old false old result Pos Step) as [value Eval]. rewrite add0n in Eval.
 exists value. split;[eapply formal_combinational_known_node;[exact Pos|exact Safe|exact Nonreg|exact Eval|eapply Shape;exact Eval|exact Step]|eapply Shape;exact Eval].
Qed.
Theorem reference_immediate_types_history invalid history limit start :
 (forall t, (t < limit)%coq_nat -> formal_value_iter invalid flat_memories (history t) false (history t) flat_statements = Some (history (S t))) ->
 (forall t, (start <= t)%coq_nat -> (t <= limit)%coq_nat -> exists value, VM.find 1884 (history t) = Some value /\ type_of_val value = Gtyp (Fuint 32)) ->
 forall i, (i < 304)%coq_nat -> forall t, (Nat.add start (reference_immediate_rank i) <= t)%coq_nat -> (t <= limit)%coq_nat ->
 exists value, VM.find (reference_immediate_node i) (history t) = Some value /\ type_of_val value = Gtyp (Fuint (reference_immediate_width i)).
Proof.
 intros Steps Source i. induction i using lt_wf_ind. intros Bound [|t] Lower Upper.
 - pose proof (proj2 (reference_immediate_plan i Bound));lia.
 - eapply reference_immediate_node_type_step;[exact Bound| |apply Steps;lia].
   intros site value Eval. eapply immediate_expression_check_sound;[exact (proj1 (reference_immediate_plan i Bound))| |exact Eval].
   intros node Member. destruct (reference_immediate_predecessors i node Bound Member) as [->|[j [Before [J [Node [Width Rank]]]]]].
   + change (exists value, VM.find 1884 (history t) = Some value /\ type_of_val value = Gtyp (Fuint 32)).
     apply Source;[pose proof (proj2 (reference_immediate_plan i Bound));lia|lia].
   + rewrite Width. rewrite <- Node. apply (H j Before J t);lia.
Qed.
