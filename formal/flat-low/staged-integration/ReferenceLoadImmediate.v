Require Import CoreSocModel ComparisonNodes ReferenceImmediateTypes ReferenceControlExpressions ReferenceControlStabilityHistory ReferenceControlNodeCongruence0 ReferenceControlNodeCongruence1 ReferenceControlNodeCongruence2 ReferenceControlNodeCertificates0 ReferenceControlNodeCertificates1 ReferenceControlNodeCertificates2 ReferenceRedirectSpine ReferenceLoadSemantics MemoryRequestObservedSemantics ReferenceMemoryRequest LoadPipelineClassification LoadImmediateSemantics DUTRedirectDecode LoadTypeCorrespondence FormalObservedHistory FormalLocalHistory ObservedJointRegisterConcrete ReferenceSystemDecode.
From Coq Require Import NArith ZArith List Lia.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From nbits Require Import NBits.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Firrtl_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Local Opaque flat_statements flat_memories generated_modules generated_top.
Lemma immediate_selected_mux invalid site old guard yes no width word other bit :
 size word = width -> VM.find guard old = Some (Gval (Fuint 1) [::bit]) ->
 VM.find (if bit then yes else no) old = Some (Gval (Fuint width) word) ->
 VM.find (if bit then no else yes) old = Some other -> type_of_val other = Gtyp (Fuint width) ->
 eval_hfexpr_validif_policy invalid site flat_memories
 (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T guard)) (@Eref VarOrder.T (@Eid VarOrder.T yes)) (@Eref VarOrder.T (@Eid VarOrder.T no))) old old = Some (Gval (Fuint width) word).
Proof.
 intros Size Guard Value Other Typed. cbn [eval_hfexpr_validif_policy eval_href_validif_policy]. rewrite Guard.
 destruct bit;cbn;rewrite Value;unfold eval_type_of_expr;cbn [type_of_expr' eval_type_of_ref];rewrite Other;cbn [option_map];rewrite Typed;
 change (adapt_hvalue_as_type (Gval (Fuint width) word) (Gtyp (Fuint (maxn width width))) = Some (Gval (Fuint width) word));rewrite maxnn;apply dut_decode_adapt;exact Size.
Qed.
Theorem immediate_stable_mux_suffix invalid old current count selected width word prefix (node guard yes:nat->VarOrder.T) :
 (selected < count)%coq_nat -> size word = width ->
 (forall n, (n < count)%coq_nat -> VM.find (node n) old = VM.find (node n) current) ->
 (forall n, (n < count)%coq_nat -> forall value,
   (forall site, eval_hfexpr_validif_policy (isolated_validif_policy invalid) site flat_memories
    (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T (guard n)))
     (@Eref VarOrder.T (@Eid VarOrder.T (yes n)))
     (@Eref VarOrder.T (@Eid VarOrder.T (match n with O => prefix | S before => node before end)))) old old = Some (Gval (Fuint width) value)) ->
   VM.find (node n) current = Some (Gval (Fuint width) value)) ->
 (forall n, (n < count)%coq_nat -> VM.find (guard n) old = Some (Gval (Fuint 1) [::Nat.eqb n selected])) ->
 (forall n, (n < count)%coq_nat -> exists value, VM.find (yes n) old = Some value /\ type_of_val value = Gtyp (Fuint width)) ->
 (forall n, (n < count)%coq_nat -> exists value, VM.find (match n with O => prefix | S before => node before end) old = Some value /\ type_of_val value = Gtyp (Fuint width)) ->
 VM.find (yes selected) old = Some (Gval (Fuint width) word) ->
 forall n, (selected <= n)%coq_nat -> (n < count)%coq_nat -> VM.find (node n) old = Some (Gval (Fuint width) word).
Proof.
 intros Selected Size Stable Node Guard YesType NoType Source n. induction n as [|n IH];intros Lower Upper.
 - assert (S : selected = 0%nat) by lia. subst selected. rewrite (Stable 0%nat Upper).
   apply (Node 0%nat Upper word). intro site. destruct (NoType 0%nat Upper) as [other [Other Typed]].
   eapply (immediate_selected_mux _ _ _ _ _ _ _ word other true);[exact Size|exact (Guard 0%nat Upper)|exact Source|exact Other|exact Typed].
 - destruct (Nat.eq_dec selected (S n)) as [Equal|Different].
   + subst selected. rewrite (Stable (S n) Upper). apply (Node (S n) Upper word). intro site.
     destruct (NoType (S n) Upper) as [other [Other Typed]].
     eapply (immediate_selected_mux _ _ _ _ _ _ _ word other true);[exact Size|rewrite <- (Nat.eqb_refl (S n));exact (Guard (S n) Upper)|exact Source|exact Other|exact Typed].
   + pose proof (IH ltac:(lia) ltac:(lia)) as Previous. rewrite (Stable (S n) Upper). apply (Node (S n) Upper word). intro site.
     destruct (YesType (S n) Upper) as [other [Other Typed]].
     assert (G : VM.find (guard (S n)) old = Some (Gval (Fuint 1) [::false])).
     { rewrite (Guard (S n) Upper). rewrite (proj2 (Nat.eqb_neq (S n) selected) ltac:(lia)). reflexivity. }
     eapply (immediate_selected_mux _ _ _ _ _ _ _ word other false);[exact Size|exact G|exact Previous|exact Other|exact Typed].
Qed.
(* Generated immediate mux certificates. *)
Definition load_imm_mux_count upper := if upper then 11%nat else 8%nat.
Definition load_imm_mux_width upper := if upper then 32%nat else 12%nat.
Definition load_imm_mux_node upper n : VarOrder.T := (if upper then 2540 else 2239)+N.of_nat n.
Definition load_imm_mux_prefix upper : VarOrder.T := if upper then 2539 else 2238.
Definition load_imm_mux_guard upper n : VarOrder.T := nth 0 (if upper then [::1970;1966;1962;1958;1886;1951;1946;1941;1937;1933;1929] else [::1970;1966;1962;1958;1886;1937;1933;1929]) n.
Definition load_imm_mux_yes upper n : VarOrder.T := nth 0 (if upper then [::2317;2313;2309;2305;2301;2297;2292;2287;2260;2256;2252] else [::2218;2217;2216;2215;2214;2213;2212;2211]) n.
Definition load_imm_mux_expression upper n := @Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T (load_imm_mux_guard upper n)))
 (@Eref VarOrder.T (@Eid VarOrder.T (load_imm_mux_yes upper n)))
 (@Eref VarOrder.T (@Eid VarOrder.T (match n with O => load_imm_mux_prefix upper | S before => load_imm_mux_node upper before end))).
Lemma load_imm_mux_member upper n : (n < load_imm_mux_count upper)%coq_nat ->
 List.In (load_imm_mux_node upper n,load_imm_mux_expression upper n) (if upper then reference_control_2_nodes else reference_control_1_nodes).
Proof. intro Bound;destruct upper.
 -
 destruct n as [|n];[exact reference_control_member_2540|].
 destruct n as [|n];[exact reference_control_member_2541|].
 destruct n as [|n];[exact reference_control_member_2542|].
 destruct n as [|n];[exact reference_control_member_2543|].
 destruct n as [|n];[exact reference_control_member_2544|].
 destruct n as [|n];[exact reference_control_member_2545|].
 destruct n as [|n];[exact reference_control_member_2546|].
 destruct n as [|n];[exact reference_control_member_2547|].
 destruct n as [|n];[exact reference_control_member_2548|].
 destruct n as [|n];[exact reference_control_member_2549|].
 destruct n as [|n];[exact reference_control_member_2550|].
 cbn [load_imm_mux_count] in Bound;lia.
 -
 destruct n as [|n];[exact reference_control_member_2239|].
 destruct n as [|n];[exact reference_control_member_2240|].
 destruct n as [|n];[exact reference_control_member_2241|].
 destruct n as [|n];[exact reference_control_member_2242|].
 destruct n as [|n];[exact reference_control_member_2243|].
 destruct n as [|n];[exact reference_control_member_2244|].
 destruct n as [|n];[exact reference_control_member_2245|].
 destruct n as [|n];[exact reference_control_member_2246|].
 cbn [load_imm_mux_count] in Bound;lia.
Qed.
Theorem load_imm_mux_node_step upper n invalid old result word :
 (n < load_imm_mux_count upper)%coq_nat ->
 (forall site, eval_hfexpr_validif_policy (isolated_validif_policy invalid) site flat_memories (load_imm_mux_expression upper n) old old = Some (Gval (Fuint (load_imm_mux_width upper)) word)) ->
 formal_value_iter invalid flat_memories old false old flat_statements = Some result ->
 VM.find (load_imm_mux_node upper n) result = Some (Gval (Fuint (load_imm_mux_width upper)) word).
Proof.
 intros Bound Eval Step. eapply (reference_redirect_ground_step (if upper then reference_control_2_offsets else reference_control_1_offsets) (if upper then reference_control_2_nodes else reference_control_1_nodes) _ (load_imm_mux_expression upper n));
 [destruct upper;[exact reference_control_2_positions|exact reference_control_1_positions]
 |destruct upper;[exact reference_control_2_safety|exact reference_control_1_safety]
 |apply load_imm_mux_member;exact Bound|exact Eval|exact Step].
Qed.
Theorem load_imm_mux_same upper n inputs path history limit reset time :
 (n < load_imm_mux_count upper)%coq_nat ->
 (forall i, (i <= limit)%coq_nat -> VM.find 1 (history i) = Some (Gval (Fuint 1) [::reset])) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 (500 <= time)%coq_nat -> (time < limit)%coq_nat ->
 VM.find (load_imm_mux_node upper n) (history time) = VM.find (load_imm_mux_node upper n) (history (S time)).
Proof. intros Bound Resets Steps Lower Upper;destruct upper.
 -
 destruct n as [|n];[apply (reference_control_stable_2540_history inputs path history limit reset Resets Steps time (S time));lia|].
 destruct n as [|n];[apply (reference_control_stable_2541_history inputs path history limit reset Resets Steps time (S time));lia|].
 destruct n as [|n];[apply (reference_control_stable_2542_history inputs path history limit reset Resets Steps time (S time));lia|].
 destruct n as [|n];[apply (reference_control_stable_2543_history inputs path history limit reset Resets Steps time (S time));lia|].
 destruct n as [|n];[apply (reference_control_stable_2544_history inputs path history limit reset Resets Steps time (S time));lia|].
 destruct n as [|n];[apply (reference_control_stable_2545_history inputs path history limit reset Resets Steps time (S time));lia|].
 destruct n as [|n];[apply (reference_control_stable_2546_history inputs path history limit reset Resets Steps time (S time));lia|].
 destruct n as [|n];[apply (reference_control_stable_2547_history inputs path history limit reset Resets Steps time (S time));lia|].
 destruct n as [|n];[apply (reference_control_stable_2548_history inputs path history limit reset Resets Steps time (S time));lia|].
 destruct n as [|n];[apply (reference_control_stable_2549_history inputs path history limit reset Resets Steps time (S time));lia|].
 destruct n as [|n];[apply (reference_control_stable_2550_history inputs path history limit reset Resets Steps time (S time));lia|].
 cbn [load_imm_mux_count] in Bound;lia.
 -
 destruct n as [|n];[apply (reference_control_stable_2239_history inputs path history limit reset Resets Steps time (S time));lia|].
 destruct n as [|n];[apply (reference_control_stable_2240_history inputs path history limit reset Resets Steps time (S time));lia|].
 destruct n as [|n];[apply (reference_control_stable_2241_history inputs path history limit reset Resets Steps time (S time));lia|].
 destruct n as [|n];[apply (reference_control_stable_2242_history inputs path history limit reset Resets Steps time (S time));lia|].
 destruct n as [|n];[apply (reference_control_stable_2243_history inputs path history limit reset Resets Steps time (S time));lia|].
 destruct n as [|n];[apply (reference_control_stable_2244_history inputs path history limit reset Resets Steps time (S time));lia|].
 destruct n as [|n];[apply (reference_control_stable_2245_history inputs path history limit reset Resets Steps time (S time));lia|].
 destruct n as [|n];[apply (reference_control_stable_2246_history inputs path history limit reset Resets Steps time (S time));lia|].
 cbn [load_imm_mux_count] in Bound;lia.
Qed.
Theorem load_imm_mux_branch_types upper n invalid history limit time :
 (n < load_imm_mux_count upper)%coq_nat ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter invalid flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 (forall i, (200 <= i)%coq_nat -> (i <= limit)%coq_nat -> exists value, VM.find 1884 (history i) = Some value /\ type_of_val value = Gtyp (Fuint 32)) ->
 (500 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 (exists value, VM.find (load_imm_mux_yes upper n) (history time) = Some value /\ type_of_val value = Gtyp (Fuint (load_imm_mux_width upper))) /\
 (exists value, VM.find (match n with O => load_imm_mux_prefix upper | S before => load_imm_mux_node upper before end) (history time) = Some value /\ type_of_val value = Gtyp (Fuint (load_imm_mux_width upper))).
Proof.
 intros Bound Steps Source Lower Upper;destruct upper.
 -
 destruct n as [|n].
 { split.
 - exact (reference_immediate_types_history invalid history limit 200 Steps Source 108%nat ltac:(vm_compute;lia) time ltac:(cbv [reference_immediate_rank reference_immediate_ranks nth];lia) Upper).
 - exact (reference_immediate_types_history invalid history limit 200 Steps Source 290%nat ltac:(vm_compute;lia) time ltac:(cbv [reference_immediate_rank reference_immediate_ranks nth];lia) Upper).
 }
 destruct n as [|n].
 { split.
 - exact (reference_immediate_types_history invalid history limit 200 Steps Source 106%nat ltac:(vm_compute;lia) time ltac:(cbv [reference_immediate_rank reference_immediate_ranks nth];lia) Upper).
 - exact (reference_immediate_types_history invalid history limit 200 Steps Source 291%nat ltac:(vm_compute;lia) time ltac:(cbv [reference_immediate_rank reference_immediate_ranks nth];lia) Upper).
 }
 destruct n as [|n].
 { split.
 - exact (reference_immediate_types_history invalid history limit 200 Steps Source 104%nat ltac:(vm_compute;lia) time ltac:(cbv [reference_immediate_rank reference_immediate_ranks nth];lia) Upper).
 - exact (reference_immediate_types_history invalid history limit 200 Steps Source 292%nat ltac:(vm_compute;lia) time ltac:(cbv [reference_immediate_rank reference_immediate_ranks nth];lia) Upper).
 }
 destruct n as [|n].
 { split.
 - exact (reference_immediate_types_history invalid history limit 200 Steps Source 102%nat ltac:(vm_compute;lia) time ltac:(cbv [reference_immediate_rank reference_immediate_ranks nth];lia) Upper).
 - exact (reference_immediate_types_history invalid history limit 200 Steps Source 293%nat ltac:(vm_compute;lia) time ltac:(cbv [reference_immediate_rank reference_immediate_ranks nth];lia) Upper).
 }
 destruct n as [|n].
 { split.
 - exact (reference_immediate_types_history invalid history limit 200 Steps Source 100%nat ltac:(vm_compute;lia) time ltac:(cbv [reference_immediate_rank reference_immediate_ranks nth];lia) Upper).
 - exact (reference_immediate_types_history invalid history limit 200 Steps Source 294%nat ltac:(vm_compute;lia) time ltac:(cbv [reference_immediate_rank reference_immediate_ranks nth];lia) Upper).
 }
 destruct n as [|n].
 { split.
 - exact (reference_immediate_types_history invalid history limit 200 Steps Source 98%nat ltac:(vm_compute;lia) time ltac:(cbv [reference_immediate_rank reference_immediate_ranks nth];lia) Upper).
 - exact (reference_immediate_types_history invalid history limit 200 Steps Source 295%nat ltac:(vm_compute;lia) time ltac:(cbv [reference_immediate_rank reference_immediate_ranks nth];lia) Upper).
 }
 destruct n as [|n].
 { split.
 - exact (reference_immediate_types_history invalid history limit 200 Steps Source 95%nat ltac:(vm_compute;lia) time ltac:(cbv [reference_immediate_rank reference_immediate_ranks nth];lia) Upper).
 - exact (reference_immediate_types_history invalid history limit 200 Steps Source 296%nat ltac:(vm_compute;lia) time ltac:(cbv [reference_immediate_rank reference_immediate_ranks nth];lia) Upper).
 }
 destruct n as [|n].
 { split.
 - exact (reference_immediate_types_history invalid history limit 200 Steps Source 92%nat ltac:(vm_compute;lia) time ltac:(cbv [reference_immediate_rank reference_immediate_ranks nth];lia) Upper).
 - exact (reference_immediate_types_history invalid history limit 200 Steps Source 297%nat ltac:(vm_compute;lia) time ltac:(cbv [reference_immediate_rank reference_immediate_ranks nth];lia) Upper).
 }
 destruct n as [|n].
 { split.
 - exact (reference_immediate_types_history invalid history limit 200 Steps Source 67%nat ltac:(vm_compute;lia) time ltac:(cbv [reference_immediate_rank reference_immediate_ranks nth];lia) Upper).
 - exact (reference_immediate_types_history invalid history limit 200 Steps Source 298%nat ltac:(vm_compute;lia) time ltac:(cbv [reference_immediate_rank reference_immediate_ranks nth];lia) Upper).
 }
 destruct n as [|n].
 { split.
 - exact (reference_immediate_types_history invalid history limit 200 Steps Source 65%nat ltac:(vm_compute;lia) time ltac:(cbv [reference_immediate_rank reference_immediate_ranks nth];lia) Upper).
 - exact (reference_immediate_types_history invalid history limit 200 Steps Source 299%nat ltac:(vm_compute;lia) time ltac:(cbv [reference_immediate_rank reference_immediate_ranks nth];lia) Upper).
 }
 destruct n as [|n].
 { split.
 - exact (reference_immediate_types_history invalid history limit 200 Steps Source 63%nat ltac:(vm_compute;lia) time ltac:(cbv [reference_immediate_rank reference_immediate_ranks nth];lia) Upper).
 - exact (reference_immediate_types_history invalid history limit 200 Steps Source 300%nat ltac:(vm_compute;lia) time ltac:(cbv [reference_immediate_rank reference_immediate_ranks nth];lia) Upper).
 }
 cbn [load_imm_mux_count] in Bound;lia.
 -
 destruct n as [|n].
 { split.
 - exact (reference_immediate_types_history invalid history limit 200 Steps Source 31%nat ltac:(vm_compute;lia) time ltac:(cbv [reference_immediate_rank reference_immediate_ranks nth];lia) Upper).
 - exact (reference_immediate_types_history invalid history limit 200 Steps Source 51%nat ltac:(vm_compute;lia) time ltac:(cbv [reference_immediate_rank reference_immediate_ranks nth];lia) Upper).
 }
 destruct n as [|n].
 { split.
 - exact (reference_immediate_types_history invalid history limit 200 Steps Source 30%nat ltac:(vm_compute;lia) time ltac:(cbv [reference_immediate_rank reference_immediate_ranks nth];lia) Upper).
 - exact (reference_immediate_types_history invalid history limit 200 Steps Source 52%nat ltac:(vm_compute;lia) time ltac:(cbv [reference_immediate_rank reference_immediate_ranks nth];lia) Upper).
 }
 destruct n as [|n].
 { split.
 - exact (reference_immediate_types_history invalid history limit 200 Steps Source 29%nat ltac:(vm_compute;lia) time ltac:(cbv [reference_immediate_rank reference_immediate_ranks nth];lia) Upper).
 - exact (reference_immediate_types_history invalid history limit 200 Steps Source 53%nat ltac:(vm_compute;lia) time ltac:(cbv [reference_immediate_rank reference_immediate_ranks nth];lia) Upper).
 }
 destruct n as [|n].
 { split.
 - exact (reference_immediate_types_history invalid history limit 200 Steps Source 28%nat ltac:(vm_compute;lia) time ltac:(cbv [reference_immediate_rank reference_immediate_ranks nth];lia) Upper).
 - exact (reference_immediate_types_history invalid history limit 200 Steps Source 54%nat ltac:(vm_compute;lia) time ltac:(cbv [reference_immediate_rank reference_immediate_ranks nth];lia) Upper).
 }
 destruct n as [|n].
 { split.
 - exact (reference_immediate_types_history invalid history limit 200 Steps Source 27%nat ltac:(vm_compute;lia) time ltac:(cbv [reference_immediate_rank reference_immediate_ranks nth];lia) Upper).
 - exact (reference_immediate_types_history invalid history limit 200 Steps Source 55%nat ltac:(vm_compute;lia) time ltac:(cbv [reference_immediate_rank reference_immediate_ranks nth];lia) Upper).
 }
 destruct n as [|n].
 { split.
 - exact (reference_immediate_types_history invalid history limit 200 Steps Source 26%nat ltac:(vm_compute;lia) time ltac:(cbv [reference_immediate_rank reference_immediate_ranks nth];lia) Upper).
 - exact (reference_immediate_types_history invalid history limit 200 Steps Source 56%nat ltac:(vm_compute;lia) time ltac:(cbv [reference_immediate_rank reference_immediate_ranks nth];lia) Upper).
 }
 destruct n as [|n].
 { split.
 - exact (reference_immediate_types_history invalid history limit 200 Steps Source 25%nat ltac:(vm_compute;lia) time ltac:(cbv [reference_immediate_rank reference_immediate_ranks nth];lia) Upper).
 - exact (reference_immediate_types_history invalid history limit 200 Steps Source 57%nat ltac:(vm_compute;lia) time ltac:(cbv [reference_immediate_rank reference_immediate_ranks nth];lia) Upper).
 }
 destruct n as [|n].
 { split.
 - exact (reference_immediate_types_history invalid history limit 200 Steps Source 24%nat ltac:(vm_compute;lia) time ltac:(cbv [reference_immediate_rank reference_immediate_ranks nth];lia) Upper).
 - exact (reference_immediate_types_history invalid history limit 200 Steps Source 58%nat ltac:(vm_compute;lia) time ltac:(cbv [reference_immediate_rank reference_immediate_ranks nth];lia) Upper).
 }
 cbn [load_imm_mux_count] in Bound;lia.
Qed.
Definition load_imm_aux_ids : seq VarOrder.T := [::2214;2215;2216;2217;2218;2247;2248;2298;2299;2300;2301;2302;2303;2304;2305;2306;2307;2308;2309;2310;2311;2312;2313;2314;2315;2316;2317;2551;2552].
Definition load_imm_aux_expressions : seq (hfexpr VarOrder.T) := [::reference_control_expr_2214;reference_control_expr_2215;reference_control_expr_2216;reference_control_expr_2217;reference_control_expr_2218;reference_control_expr_2247;reference_control_expr_2248;reference_control_expr_2298;reference_control_expr_2299;reference_control_expr_2300;reference_control_expr_2301;reference_control_expr_2302;reference_control_expr_2303;reference_control_expr_2304;reference_control_expr_2305;reference_control_expr_2306;reference_control_expr_2307;reference_control_expr_2308;reference_control_expr_2309;reference_control_expr_2310;reference_control_expr_2311;reference_control_expr_2312;reference_control_expr_2313;reference_control_expr_2314;reference_control_expr_2315;reference_control_expr_2316;reference_control_expr_2317;reference_control_expr_2551;reference_control_expr_2552].
Definition load_imm_aux_node i := nth 0 load_imm_aux_ids i.
Definition load_imm_aux_expression i := nth (@Econst VarOrder.T (Fuint 1) [::false]) load_imm_aux_expressions i.
Definition load_imm_aux_nodes i := if Nat.ltb i 27 then reference_control_1_nodes else reference_control_2_nodes.
Definition load_imm_aux_offsets i := if Nat.ltb i 27 then reference_control_1_offsets else reference_control_2_offsets.
Lemma load_imm_aux_member i : (i < 29)%coq_nat -> List.In (load_imm_aux_node i,load_imm_aux_expression i) (load_imm_aux_nodes i).
Proof. intro Bound.
 destruct i as [|i];[exact reference_control_member_2214|].
 destruct i as [|i];[exact reference_control_member_2215|].
 destruct i as [|i];[exact reference_control_member_2216|].
 destruct i as [|i];[exact reference_control_member_2217|].
 destruct i as [|i];[exact reference_control_member_2218|].
 destruct i as [|i];[exact reference_control_member_2247|].
 destruct i as [|i];[exact reference_control_member_2248|].
 destruct i as [|i];[exact reference_control_member_2298|].
 destruct i as [|i];[exact reference_control_member_2299|].
 destruct i as [|i];[exact reference_control_member_2300|].
 destruct i as [|i];[exact reference_control_member_2301|].
 destruct i as [|i];[exact reference_control_member_2302|].
 destruct i as [|i];[exact reference_control_member_2303|].
 destruct i as [|i];[exact reference_control_member_2304|].
 destruct i as [|i];[exact reference_control_member_2305|].
 destruct i as [|i];[exact reference_control_member_2306|].
 destruct i as [|i];[exact reference_control_member_2307|].
 destruct i as [|i];[exact reference_control_member_2308|].
 destruct i as [|i];[exact reference_control_member_2309|].
 destruct i as [|i];[exact reference_control_member_2310|].
 destruct i as [|i];[exact reference_control_member_2311|].
 destruct i as [|i];[exact reference_control_member_2312|].
 destruct i as [|i];[exact reference_control_member_2313|].
 destruct i as [|i];[exact reference_control_member_2314|].
 destruct i as [|i];[exact reference_control_member_2315|].
 destruct i as [|i];[exact reference_control_member_2316|].
 destruct i as [|i];[exact reference_control_member_2317|].
 destruct i as [|i];[exact reference_control_member_2551|].
 destruct i as [|i];[exact reference_control_member_2552|].
 lia.
Qed.
Theorem load_imm_aux_value i inputs path history limit reset time width word :
 (i < 29)%coq_nat ->
 (forall t, (t <= limit)%coq_nat -> VM.find 1 (history t) = Some (Gval (Fuint 1) [::reset])) ->
 (forall t, (t < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history t) false (history t) flat_statements = Some (history (S t))) ->
 (500 <= time)%coq_nat -> (time < limit)%coq_nat ->
 (forall site, eval_hfexpr_validif_policy (isolated_validif_policy (formal_invalid_policy inputs path)) site flat_memories (load_imm_aux_expression i) (history time) (history time) = Some (Gval (Fuint width) word)) ->
 VM.find (load_imm_aux_node i) (history time) = Some (Gval (Fuint width) word).
Proof.
 intros Bound Resets Steps Lower Upper Eval.
 assert (Stable : VM.find (load_imm_aux_node i) (history time) = VM.find (load_imm_aux_node i) (history (S time))).
 {
 destruct i as [|i];[apply (reference_control_stable_2214_history inputs path history limit reset Resets Steps time (S time));lia|].
 destruct i as [|i];[apply (reference_control_stable_2215_history inputs path history limit reset Resets Steps time (S time));lia|].
 destruct i as [|i];[apply (reference_control_stable_2216_history inputs path history limit reset Resets Steps time (S time));lia|].
 destruct i as [|i];[apply (reference_control_stable_2217_history inputs path history limit reset Resets Steps time (S time));lia|].
 destruct i as [|i];[apply (reference_control_stable_2218_history inputs path history limit reset Resets Steps time (S time));lia|].
 destruct i as [|i];[apply (reference_control_stable_2247_history inputs path history limit reset Resets Steps time (S time));lia|].
 destruct i as [|i];[apply (reference_control_stable_2248_history inputs path history limit reset Resets Steps time (S time));lia|].
 destruct i as [|i];[apply (reference_control_stable_2298_history inputs path history limit reset Resets Steps time (S time));lia|].
 destruct i as [|i];[apply (reference_control_stable_2299_history inputs path history limit reset Resets Steps time (S time));lia|].
 destruct i as [|i];[apply (reference_control_stable_2300_history inputs path history limit reset Resets Steps time (S time));lia|].
 destruct i as [|i];[apply (reference_control_stable_2301_history inputs path history limit reset Resets Steps time (S time));lia|].
 destruct i as [|i];[apply (reference_control_stable_2302_history inputs path history limit reset Resets Steps time (S time));lia|].
 destruct i as [|i];[apply (reference_control_stable_2303_history inputs path history limit reset Resets Steps time (S time));lia|].
 destruct i as [|i];[apply (reference_control_stable_2304_history inputs path history limit reset Resets Steps time (S time));lia|].
 destruct i as [|i];[apply (reference_control_stable_2305_history inputs path history limit reset Resets Steps time (S time));lia|].
 destruct i as [|i];[apply (reference_control_stable_2306_history inputs path history limit reset Resets Steps time (S time));lia|].
 destruct i as [|i];[apply (reference_control_stable_2307_history inputs path history limit reset Resets Steps time (S time));lia|].
 destruct i as [|i];[apply (reference_control_stable_2308_history inputs path history limit reset Resets Steps time (S time));lia|].
 destruct i as [|i];[apply (reference_control_stable_2309_history inputs path history limit reset Resets Steps time (S time));lia|].
 destruct i as [|i];[apply (reference_control_stable_2310_history inputs path history limit reset Resets Steps time (S time));lia|].
 destruct i as [|i];[apply (reference_control_stable_2311_history inputs path history limit reset Resets Steps time (S time));lia|].
 destruct i as [|i];[apply (reference_control_stable_2312_history inputs path history limit reset Resets Steps time (S time));lia|].
 destruct i as [|i];[apply (reference_control_stable_2313_history inputs path history limit reset Resets Steps time (S time));lia|].
 destruct i as [|i];[apply (reference_control_stable_2314_history inputs path history limit reset Resets Steps time (S time));lia|].
 destruct i as [|i];[apply (reference_control_stable_2315_history inputs path history limit reset Resets Steps time (S time));lia|].
 destruct i as [|i];[apply (reference_control_stable_2316_history inputs path history limit reset Resets Steps time (S time));lia|].
 destruct i as [|i];[apply (reference_control_stable_2317_history inputs path history limit reset Resets Steps time (S time));lia|].
 destruct i as [|i];[apply (reference_control_stable_2551_history inputs path history limit reset Resets Steps time (S time));lia|].
 destruct i as [|i];[apply (reference_control_stable_2552_history inputs path history limit reset Resets Steps time (S time));lia|].
 lia. }
 rewrite Stable. eapply (reference_redirect_ground_step (load_imm_aux_offsets i) (load_imm_aux_nodes i) _ (load_imm_aux_expression i));
 [unfold load_imm_aux_offsets,load_imm_aux_nodes;destruct (Nat.ltb i 27);[exact reference_control_1_positions|exact reference_control_2_positions]
 |unfold load_imm_aux_offsets;destruct (Nat.ltb i 27);[exact reference_control_1_safety|exact reference_control_2_safety]
 |apply load_imm_aux_member;exact Bound|exact Eval|apply Steps;exact Upper].
Qed.
(* Actual load immediate semantics. *)
Lemma load_imm_guards_selected old lane :
 (lane < 5)%coq_nat ->
 (forall row, (row < 8)%coq_nat -> VM.find (reference_memory_guard row) old = Some (Gval (Fuint 1) [::Nat.eqb row lane])) ->
 VM.find 1929 old = Some (Gval (Fuint 1) [::false]) ->
 VM.find 1933 old = Some (Gval (Fuint 1) [::false]) ->
 VM.find 1937 old = Some (Gval (Fuint 1) [::false]) ->
 forall upper n, (n < load_imm_mux_count upper)%coq_nat ->
 VM.find (load_imm_mux_guard upper n) old = Some (Gval (Fuint 1) [::Nat.eqb n (Nat.sub 4 lane)]).
Proof.
 intros Lane Guards Fence Ecall Ebreak.
 pose proof (Guards 0%nat ltac:(lia)) as G0.
 pose proof (Guards 1%nat ltac:(lia)) as G1.
 pose proof (Guards 2%nat ltac:(lia)) as G2.
 pose proof (Guards 3%nat ltac:(lia)) as G3.
 pose proof (Guards 4%nat ltac:(lia)) as G4.
 pose proof (Guards 5%nat ltac:(lia)) as G5.
 pose proof (Guards 6%nat ltac:(lia)) as G6.
 pose proof (Guards 7%nat ltac:(lia)) as G7.
 cbn [reference_memory_guard reference_memory_guards nth] in G0,G1,G2,G3,G4,G5,G6,G7.
 intros upper n Bound.
 destruct upper.
 -
 destruct n as [|n].
 { destruct lane as [|lane];[cbn [load_imm_mux_guard nth Nat.sub Nat.eqb] in *;assumption|]. destruct lane as [|lane];[cbn [load_imm_mux_guard nth Nat.sub Nat.eqb] in *;assumption|]. destruct lane as [|lane];[cbn [load_imm_mux_guard nth Nat.sub Nat.eqb] in *;assumption|]. destruct lane as [|lane];[cbn [load_imm_mux_guard nth Nat.sub Nat.eqb] in *;assumption|]. destruct lane as [|lane];[cbn [load_imm_mux_guard nth Nat.sub Nat.eqb] in *;assumption|]. lia. }
 destruct n as [|n].
 { destruct lane as [|lane];[cbn [load_imm_mux_guard nth Nat.sub Nat.eqb] in *;assumption|]. destruct lane as [|lane];[cbn [load_imm_mux_guard nth Nat.sub Nat.eqb] in *;assumption|]. destruct lane as [|lane];[cbn [load_imm_mux_guard nth Nat.sub Nat.eqb] in *;assumption|]. destruct lane as [|lane];[cbn [load_imm_mux_guard nth Nat.sub Nat.eqb] in *;assumption|]. destruct lane as [|lane];[cbn [load_imm_mux_guard nth Nat.sub Nat.eqb] in *;assumption|]. lia. }
 destruct n as [|n].
 { destruct lane as [|lane];[cbn [load_imm_mux_guard nth Nat.sub Nat.eqb] in *;assumption|]. destruct lane as [|lane];[cbn [load_imm_mux_guard nth Nat.sub Nat.eqb] in *;assumption|]. destruct lane as [|lane];[cbn [load_imm_mux_guard nth Nat.sub Nat.eqb] in *;assumption|]. destruct lane as [|lane];[cbn [load_imm_mux_guard nth Nat.sub Nat.eqb] in *;assumption|]. destruct lane as [|lane];[cbn [load_imm_mux_guard nth Nat.sub Nat.eqb] in *;assumption|]. lia. }
 destruct n as [|n].
 { destruct lane as [|lane];[cbn [load_imm_mux_guard nth Nat.sub Nat.eqb] in *;assumption|]. destruct lane as [|lane];[cbn [load_imm_mux_guard nth Nat.sub Nat.eqb] in *;assumption|]. destruct lane as [|lane];[cbn [load_imm_mux_guard nth Nat.sub Nat.eqb] in *;assumption|]. destruct lane as [|lane];[cbn [load_imm_mux_guard nth Nat.sub Nat.eqb] in *;assumption|]. destruct lane as [|lane];[cbn [load_imm_mux_guard nth Nat.sub Nat.eqb] in *;assumption|]. lia. }
 destruct n as [|n].
 { destruct lane as [|lane];[cbn [load_imm_mux_guard nth Nat.sub Nat.eqb] in *;assumption|]. destruct lane as [|lane];[cbn [load_imm_mux_guard nth Nat.sub Nat.eqb] in *;assumption|]. destruct lane as [|lane];[cbn [load_imm_mux_guard nth Nat.sub Nat.eqb] in *;assumption|]. destruct lane as [|lane];[cbn [load_imm_mux_guard nth Nat.sub Nat.eqb] in *;assumption|]. destruct lane as [|lane];[cbn [load_imm_mux_guard nth Nat.sub Nat.eqb] in *;assumption|]. lia. }
 destruct n as [|n].
 { destruct lane as [|lane];[cbn [load_imm_mux_guard nth Nat.sub Nat.eqb] in *;assumption|]. destruct lane as [|lane];[cbn [load_imm_mux_guard nth Nat.sub Nat.eqb] in *;assumption|]. destruct lane as [|lane];[cbn [load_imm_mux_guard nth Nat.sub Nat.eqb] in *;assumption|]. destruct lane as [|lane];[cbn [load_imm_mux_guard nth Nat.sub Nat.eqb] in *;assumption|]. destruct lane as [|lane];[cbn [load_imm_mux_guard nth Nat.sub Nat.eqb] in *;assumption|]. lia. }
 destruct n as [|n].
 { destruct lane as [|lane];[cbn [load_imm_mux_guard nth Nat.sub Nat.eqb] in *;assumption|]. destruct lane as [|lane];[cbn [load_imm_mux_guard nth Nat.sub Nat.eqb] in *;assumption|]. destruct lane as [|lane];[cbn [load_imm_mux_guard nth Nat.sub Nat.eqb] in *;assumption|]. destruct lane as [|lane];[cbn [load_imm_mux_guard nth Nat.sub Nat.eqb] in *;assumption|]. destruct lane as [|lane];[cbn [load_imm_mux_guard nth Nat.sub Nat.eqb] in *;assumption|]. lia. }
 destruct n as [|n].
 { destruct lane as [|lane];[cbn [load_imm_mux_guard nth Nat.sub Nat.eqb] in *;assumption|]. destruct lane as [|lane];[cbn [load_imm_mux_guard nth Nat.sub Nat.eqb] in *;assumption|]. destruct lane as [|lane];[cbn [load_imm_mux_guard nth Nat.sub Nat.eqb] in *;assumption|]. destruct lane as [|lane];[cbn [load_imm_mux_guard nth Nat.sub Nat.eqb] in *;assumption|]. destruct lane as [|lane];[cbn [load_imm_mux_guard nth Nat.sub Nat.eqb] in *;assumption|]. lia. }
 destruct n as [|n].
 { destruct lane as [|lane];[cbn [load_imm_mux_guard nth Nat.sub Nat.eqb] in *;assumption|]. destruct lane as [|lane];[cbn [load_imm_mux_guard nth Nat.sub Nat.eqb] in *;assumption|]. destruct lane as [|lane];[cbn [load_imm_mux_guard nth Nat.sub Nat.eqb] in *;assumption|]. destruct lane as [|lane];[cbn [load_imm_mux_guard nth Nat.sub Nat.eqb] in *;assumption|]. destruct lane as [|lane];[cbn [load_imm_mux_guard nth Nat.sub Nat.eqb] in *;assumption|]. lia. }
 destruct n as [|n].
 { destruct lane as [|lane];[cbn [load_imm_mux_guard nth Nat.sub Nat.eqb] in *;assumption|]. destruct lane as [|lane];[cbn [load_imm_mux_guard nth Nat.sub Nat.eqb] in *;assumption|]. destruct lane as [|lane];[cbn [load_imm_mux_guard nth Nat.sub Nat.eqb] in *;assumption|]. destruct lane as [|lane];[cbn [load_imm_mux_guard nth Nat.sub Nat.eqb] in *;assumption|]. destruct lane as [|lane];[cbn [load_imm_mux_guard nth Nat.sub Nat.eqb] in *;assumption|]. lia. }
 destruct n as [|n].
 { destruct lane as [|lane];[cbn [load_imm_mux_guard nth Nat.sub Nat.eqb] in *;assumption|]. destruct lane as [|lane];[cbn [load_imm_mux_guard nth Nat.sub Nat.eqb] in *;assumption|]. destruct lane as [|lane];[cbn [load_imm_mux_guard nth Nat.sub Nat.eqb] in *;assumption|]. destruct lane as [|lane];[cbn [load_imm_mux_guard nth Nat.sub Nat.eqb] in *;assumption|]. destruct lane as [|lane];[cbn [load_imm_mux_guard nth Nat.sub Nat.eqb] in *;assumption|]. lia. }
 cbn [load_imm_mux_count] in Bound;lia.
 -
 destruct n as [|n].
 { destruct lane as [|lane];[cbn [load_imm_mux_guard nth Nat.sub Nat.eqb] in *;assumption|]. destruct lane as [|lane];[cbn [load_imm_mux_guard nth Nat.sub Nat.eqb] in *;assumption|]. destruct lane as [|lane];[cbn [load_imm_mux_guard nth Nat.sub Nat.eqb] in *;assumption|]. destruct lane as [|lane];[cbn [load_imm_mux_guard nth Nat.sub Nat.eqb] in *;assumption|]. destruct lane as [|lane];[cbn [load_imm_mux_guard nth Nat.sub Nat.eqb] in *;assumption|]. lia. }
 destruct n as [|n].
 { destruct lane as [|lane];[cbn [load_imm_mux_guard nth Nat.sub Nat.eqb] in *;assumption|]. destruct lane as [|lane];[cbn [load_imm_mux_guard nth Nat.sub Nat.eqb] in *;assumption|]. destruct lane as [|lane];[cbn [load_imm_mux_guard nth Nat.sub Nat.eqb] in *;assumption|]. destruct lane as [|lane];[cbn [load_imm_mux_guard nth Nat.sub Nat.eqb] in *;assumption|]. destruct lane as [|lane];[cbn [load_imm_mux_guard nth Nat.sub Nat.eqb] in *;assumption|]. lia. }
 destruct n as [|n].
 { destruct lane as [|lane];[cbn [load_imm_mux_guard nth Nat.sub Nat.eqb] in *;assumption|]. destruct lane as [|lane];[cbn [load_imm_mux_guard nth Nat.sub Nat.eqb] in *;assumption|]. destruct lane as [|lane];[cbn [load_imm_mux_guard nth Nat.sub Nat.eqb] in *;assumption|]. destruct lane as [|lane];[cbn [load_imm_mux_guard nth Nat.sub Nat.eqb] in *;assumption|]. destruct lane as [|lane];[cbn [load_imm_mux_guard nth Nat.sub Nat.eqb] in *;assumption|]. lia. }
 destruct n as [|n].
 { destruct lane as [|lane];[cbn [load_imm_mux_guard nth Nat.sub Nat.eqb] in *;assumption|]. destruct lane as [|lane];[cbn [load_imm_mux_guard nth Nat.sub Nat.eqb] in *;assumption|]. destruct lane as [|lane];[cbn [load_imm_mux_guard nth Nat.sub Nat.eqb] in *;assumption|]. destruct lane as [|lane];[cbn [load_imm_mux_guard nth Nat.sub Nat.eqb] in *;assumption|]. destruct lane as [|lane];[cbn [load_imm_mux_guard nth Nat.sub Nat.eqb] in *;assumption|]. lia. }
 destruct n as [|n].
 { destruct lane as [|lane];[cbn [load_imm_mux_guard nth Nat.sub Nat.eqb] in *;assumption|]. destruct lane as [|lane];[cbn [load_imm_mux_guard nth Nat.sub Nat.eqb] in *;assumption|]. destruct lane as [|lane];[cbn [load_imm_mux_guard nth Nat.sub Nat.eqb] in *;assumption|]. destruct lane as [|lane];[cbn [load_imm_mux_guard nth Nat.sub Nat.eqb] in *;assumption|]. destruct lane as [|lane];[cbn [load_imm_mux_guard nth Nat.sub Nat.eqb] in *;assumption|]. lia. }
 destruct n as [|n].
 { destruct lane as [|lane];[cbn [load_imm_mux_guard nth Nat.sub Nat.eqb] in *;assumption|]. destruct lane as [|lane];[cbn [load_imm_mux_guard nth Nat.sub Nat.eqb] in *;assumption|]. destruct lane as [|lane];[cbn [load_imm_mux_guard nth Nat.sub Nat.eqb] in *;assumption|]. destruct lane as [|lane];[cbn [load_imm_mux_guard nth Nat.sub Nat.eqb] in *;assumption|]. destruct lane as [|lane];[cbn [load_imm_mux_guard nth Nat.sub Nat.eqb] in *;assumption|]. lia. }
 destruct n as [|n].
 { destruct lane as [|lane];[cbn [load_imm_mux_guard nth Nat.sub Nat.eqb] in *;assumption|]. destruct lane as [|lane];[cbn [load_imm_mux_guard nth Nat.sub Nat.eqb] in *;assumption|]. destruct lane as [|lane];[cbn [load_imm_mux_guard nth Nat.sub Nat.eqb] in *;assumption|]. destruct lane as [|lane];[cbn [load_imm_mux_guard nth Nat.sub Nat.eqb] in *;assumption|]. destruct lane as [|lane];[cbn [load_imm_mux_guard nth Nat.sub Nat.eqb] in *;assumption|]. lia. }
 destruct n as [|n].
 { destruct lane as [|lane];[cbn [load_imm_mux_guard nth Nat.sub Nat.eqb] in *;assumption|]. destruct lane as [|lane];[cbn [load_imm_mux_guard nth Nat.sub Nat.eqb] in *;assumption|]. destruct lane as [|lane];[cbn [load_imm_mux_guard nth Nat.sub Nat.eqb] in *;assumption|]. destruct lane as [|lane];[cbn [load_imm_mux_guard nth Nat.sub Nat.eqb] in *;assumption|]. destruct lane as [|lane];[cbn [load_imm_mux_guard nth Nat.sub Nat.eqb] in *;assumption|]. lia. }
 cbn [load_imm_mux_count] in Bound;lia.
Qed.
Lemma load_imm_raw_selected inputs path history limit reset time instruction lane :
 (lane < 5)%coq_nat ->
 (forall t, (t <= limit)%coq_nat -> VM.find 1 (history t) = Some (Gval (Fuint 1) [::reset])) ->
 (forall t, (t < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history t) false (history t) flat_statements = Some (history (S t))) ->
 (500 <= time)%coq_nat -> (time < limit)%coq_nat ->
 VM.find 1884 (history time) = Some (Gval (Fuint 32) instruction) ->
 VM.find (load_imm_mux_yes false (Nat.sub 4 lane)) (history time) = Some (Gval (Fuint 12) (drop 20 (take 32 instruction))).
Proof.
 intros Lane Resets Steps Lower Upper Source.
 assert (Raw : VM.find (load_imm_aux_node lane) (history time) = Some (Gval (Fuint 12) (drop 20 (take 32 instruction)))).
 { eapply (load_imm_aux_value lane inputs path history limit reset time);[lia|exact Resets|exact Steps|exact Lower|exact Upper|].
   intro site. do 5 (destruct lane as [|lane]; [cbn [Nat.add Nat.mul load_imm_aux_expression load_imm_aux_expressions nth reference_control_expr_2214 reference_control_expr_2215 reference_control_expr_2216 reference_control_expr_2217 reference_control_expr_2218 eval_hfexpr_validif_policy eval_href_validif_policy];rewrite Source;reflexivity|]);lia. }
 do 5 (destruct lane as [|lane];[exact Raw|]);lia.
Qed.
Lemma load_imm_mux_suffix_history upper inputs path history limit reset time selected word :
 (selected < load_imm_mux_count upper)%coq_nat -> size word = load_imm_mux_width upper ->
 (forall t, (t <= limit)%coq_nat -> VM.find 1 (history t) = Some (Gval (Fuint 1) [::reset])) ->
 (forall t, (t < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history t) false (history t) flat_statements = Some (history (S t))) ->
 (forall t, (200 <= t)%coq_nat -> (t <= limit)%coq_nat -> exists value, VM.find 1884 (history t) = Some value /\ type_of_val value = Gtyp (Fuint 32)) ->
 (500 <= time)%coq_nat -> (time < limit)%coq_nat ->
 (forall n, (n < load_imm_mux_count upper)%coq_nat -> VM.find (load_imm_mux_guard upper n) (history time) = Some (Gval (Fuint 1) [::Nat.eqb n selected])) ->
 VM.find (load_imm_mux_yes upper selected) (history time) = Some (Gval (Fuint (load_imm_mux_width upper)) word) ->
 forall n, (selected <= n)%coq_nat -> (n < load_imm_mux_count upper)%coq_nat ->
 VM.find (load_imm_mux_node upper n) (history time) = Some (Gval (Fuint (load_imm_mux_width upper)) word).
Proof.
 intros Selected Size Resets Steps Source Lower Upper Guards Value.
 eapply (immediate_stable_mux_suffix (formal_invalid_policy inputs path) (history time) (history (S time)) (load_imm_mux_count upper) selected (load_imm_mux_width upper) word (load_imm_mux_prefix upper) (load_imm_mux_node upper) (load_imm_mux_guard upper) (load_imm_mux_yes upper));[exact Selected|exact Size| | |exact Guards| | |exact Value].
 - intros n Bound. exact (load_imm_mux_same upper n inputs path history limit reset time Bound Resets Steps Lower Upper).
 - intros n Bound value Eval. apply (load_imm_mux_node_step upper n _ _ _ value Bound Eval). apply Steps;exact Upper.
 - intros n Bound. exact (proj1 (load_imm_mux_branch_types upper n _ history limit time Bound Steps Source Lower ltac:(lia))).
 - intros n Bound. exact (proj2 (load_imm_mux_branch_types upper n _ history limit time Bound Steps Source Lower ltac:(lia))).
Qed.
Lemma load_imm_low_history inputs path history limit reset time instruction lane :
 (lane < 5)%coq_nat -> size instruction = 32%nat ->
 (forall t, (t <= limit)%coq_nat -> VM.find 1 (history t) = Some (Gval (Fuint 1) [::reset])) ->
 (forall t, (t < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history t) false (history t) flat_statements = Some (history (S t))) ->
 (forall t, (200 <= t)%coq_nat -> (t <= limit)%coq_nat -> VM.find 1884 (history t) = Some (Gval (Fuint 32) instruction)) ->
 (500 <= time)%coq_nat -> (time < limit)%coq_nat ->
 VM.find 1707 (history time) = Some (Gval (Fuint 1) [::true]) ->
 (forall n, (n < 8)%coq_nat -> VM.find (load_imm_mux_guard false n) (history time) = Some (Gval (Fuint 1) [::Nat.eqb n (Nat.sub 4 lane)])) ->
 VM.find 2248 (history time) = Some (Gval (Fuint 12) (drop 20 (take 32 instruction))).
Proof.
 intros Lane Size Resets Steps Source Lower Upper Enabled Guards.
 assert (LowSize : size (drop 20 (take 32 instruction)) = 12%nat) by (rewrite size_drop size_take Size;reflexivity).
 pose proof (load_imm_raw_selected inputs path history limit reset time instruction lane Lane Resets Steps Lower Upper (Source time ltac:(lia) ltac:(lia))) as Raw.
 assert (Selected : VM.find 2246 (history time) = Some (Gval (Fuint 12) (drop 20 (take 32 instruction)))).
 { change (VM.find (load_imm_mux_node false 7) (history time) = Some (Gval (Fuint (load_imm_mux_width false)) (drop 20 (take 32 instruction)))).
   eapply (load_imm_mux_suffix_history false inputs path history limit reset time (Nat.sub 4 lane) (drop 20 (take 32 instruction)));[cbn [load_imm_mux_count];lia|exact LowSize|exact Resets|exact Steps| |exact Lower|exact Upper|exact Guards|exact Raw|lia|cbn [load_imm_mux_count];lia].
   intros t L U. exists (Gval (Fuint 32) instruction);split;[apply Source;assumption|reflexivity]. }
 assert (EnabledValue : VM.find 2247 (history time) = Some (Gval (Fuint 12) (drop 20 (take 32 instruction)))).
 { eapply (load_imm_aux_value 5 inputs path history limit reset time);[lia|exact Resets|exact Steps|exact Lower|exact Upper|].
   intro site. cbn [Nat.add Nat.mul load_imm_aux_expression load_imm_aux_expressions nth reference_control_expr_2247 eval_hfexpr_validif_policy eval_href_validif_policy].
   rewrite Enabled;cbn;rewrite Selected. change (adapt_hvalue_as_type (Gval (Fuint 12) (drop 20 (take 32 instruction))) (Gtyp (Fuint 12)) = Some (Gval (Fuint 12) (drop 20 (take 32 instruction)))). apply dut_decode_adapt;exact LowSize. }
 eapply (load_imm_aux_value 6 inputs path history limit reset time);[lia|exact Resets|exact Steps|exact Lower|exact Upper|].
 intro site. exact EnabledValue.
Qed.
Lemma load_imm_sign_history inputs path history limit reset time word lane :
 (lane < 5)%coq_nat -> size word = 12%nat ->
 (forall t, (t <= limit)%coq_nat -> VM.find 1 (history t) = Some (Gval (Fuint 1) [::reset])) ->
 (forall t, (t < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history t) false (history t) flat_statements = Some (history (S t))) ->
 (500 <= time)%coq_nat -> (time < limit)%coq_nat ->
 VM.find 2248 (history time) = Some (Gval (Fuint 12) word) ->
 VM.find (load_imm_mux_yes true (Nat.sub 4 lane)) (history time) = Some (Gval (Fuint 32) (sext_to 32 word)).
Proof.
 intros Lane Size Resets Steps Lower Upper Low.
 assert (S0 : VM.find (load_imm_aux_node (Nat.add 7 (Nat.mul 4 lane))) (history time) = Some (Gval (Fuint 1) ([::msb word]))).
 { eapply (load_imm_aux_value (Nat.add 7 (Nat.mul 4 lane)) inputs path history limit reset time);[lia|exact Resets|exact Steps|exact Lower|exact Upper|].
 intro site.
 destruct lane as [|lane].
 { cbn [Nat.add Nat.mul load_imm_aux_expression load_imm_aux_expressions nth reference_control_expr_2298 eval_hfexpr_validif_policy eval_href_validif_policy]. rewrite Low. change (Some (Gval (Fuint 1) (drop (12-1)%nat (take 12 word))) = Some (Gval (Fuint 1) [::msb word])). rewrite (reference_load_sign_bit 12 word Size (eq_refl true));reflexivity. }
 destruct lane as [|lane].
 { cbn [Nat.add Nat.mul load_imm_aux_expression load_imm_aux_expressions nth reference_control_expr_2302 eval_hfexpr_validif_policy eval_href_validif_policy]. rewrite Low. change (Some (Gval (Fuint 1) (drop (12-1)%nat (take 12 word))) = Some (Gval (Fuint 1) [::msb word])). rewrite (reference_load_sign_bit 12 word Size (eq_refl true));reflexivity. }
 destruct lane as [|lane].
 { cbn [Nat.add Nat.mul load_imm_aux_expression load_imm_aux_expressions nth reference_control_expr_2306 eval_hfexpr_validif_policy eval_href_validif_policy]. rewrite Low. change (Some (Gval (Fuint 1) (drop (12-1)%nat (take 12 word))) = Some (Gval (Fuint 1) [::msb word])). rewrite (reference_load_sign_bit 12 word Size (eq_refl true));reflexivity. }
 destruct lane as [|lane].
 { cbn [Nat.add Nat.mul load_imm_aux_expression load_imm_aux_expressions nth reference_control_expr_2310 eval_hfexpr_validif_policy eval_href_validif_policy]. rewrite Low. change (Some (Gval (Fuint 1) (drop (12-1)%nat (take 12 word))) = Some (Gval (Fuint 1) [::msb word])). rewrite (reference_load_sign_bit 12 word Size (eq_refl true));reflexivity. }
 destruct lane as [|lane].
 { cbn [Nat.add Nat.mul load_imm_aux_expression load_imm_aux_expressions nth reference_control_expr_2314 eval_hfexpr_validif_policy eval_href_validif_policy]. rewrite Low. change (Some (Gval (Fuint 1) (drop (12-1)%nat (take 12 word))) = Some (Gval (Fuint 1) [::msb word])). rewrite (reference_load_sign_bit 12 word Size (eq_refl true));reflexivity. }
lia. }
 assert (S1 : VM.find (load_imm_aux_node (Nat.add 8 (Nat.mul 4 lane))) (history time) = Some (Gval (Fuint 1) ([::msb word]))).
 { eapply (load_imm_aux_value (Nat.add 8 (Nat.mul 4 lane)) inputs path history limit reset time);[lia|exact Resets|exact Steps|exact Lower|exact Upper|].
 intro site.
 destruct lane as [|lane].
 { cbn [Nat.add Nat.mul load_imm_aux_node load_imm_aux_ids nth] in S0. cbn [Nat.add Nat.mul load_imm_aux_expression load_imm_aux_expressions nth reference_control_expr_2299 eval_hfexpr_validif_policy eval_href_validif_policy]. rewrite S0;reflexivity. }
 destruct lane as [|lane].
 { cbn [Nat.add Nat.mul load_imm_aux_node load_imm_aux_ids nth] in S0. cbn [Nat.add Nat.mul load_imm_aux_expression load_imm_aux_expressions nth reference_control_expr_2303 eval_hfexpr_validif_policy eval_href_validif_policy]. rewrite S0;reflexivity. }
 destruct lane as [|lane].
 { cbn [Nat.add Nat.mul load_imm_aux_node load_imm_aux_ids nth] in S0. cbn [Nat.add Nat.mul load_imm_aux_expression load_imm_aux_expressions nth reference_control_expr_2307 eval_hfexpr_validif_policy eval_href_validif_policy]. rewrite S0;reflexivity. }
 destruct lane as [|lane].
 { cbn [Nat.add Nat.mul load_imm_aux_node load_imm_aux_ids nth] in S0. cbn [Nat.add Nat.mul load_imm_aux_expression load_imm_aux_expressions nth reference_control_expr_2311 eval_hfexpr_validif_policy eval_href_validif_policy]. rewrite S0;reflexivity. }
 destruct lane as [|lane].
 { cbn [Nat.add Nat.mul load_imm_aux_node load_imm_aux_ids nth] in S0. cbn [Nat.add Nat.mul load_imm_aux_expression load_imm_aux_expressions nth reference_control_expr_2315 eval_hfexpr_validif_policy eval_href_validif_policy]. rewrite S0;reflexivity. }
lia. }
 assert (S2 : VM.find (load_imm_aux_node (Nat.add 9 (Nat.mul 4 lane))) (history time) = Some (Gval (Fuint 20) (nseq 20 (msb word)))).
 { eapply (load_imm_aux_value (Nat.add 9 (Nat.mul 4 lane)) inputs path history limit reset time);[lia|exact Resets|exact Steps|exact Lower|exact Upper|].
 intro site.
 destruct lane as [|lane].
 { cbn [Nat.add Nat.mul load_imm_aux_node load_imm_aux_ids nth] in S1. cbn [Nat.add Nat.mul load_imm_aux_expression load_imm_aux_expressions nth reference_control_expr_2300 eval_hfexpr_validif_policy eval_href_validif_policy]. rewrite S1;destruct (msb word);reflexivity. }
 destruct lane as [|lane].
 { cbn [Nat.add Nat.mul load_imm_aux_node load_imm_aux_ids nth] in S1. cbn [Nat.add Nat.mul load_imm_aux_expression load_imm_aux_expressions nth reference_control_expr_2304 eval_hfexpr_validif_policy eval_href_validif_policy]. rewrite S1;destruct (msb word);reflexivity. }
 destruct lane as [|lane].
 { cbn [Nat.add Nat.mul load_imm_aux_node load_imm_aux_ids nth] in S1. cbn [Nat.add Nat.mul load_imm_aux_expression load_imm_aux_expressions nth reference_control_expr_2308 eval_hfexpr_validif_policy eval_href_validif_policy]. rewrite S1;destruct (msb word);reflexivity. }
 destruct lane as [|lane].
 { cbn [Nat.add Nat.mul load_imm_aux_node load_imm_aux_ids nth] in S1. cbn [Nat.add Nat.mul load_imm_aux_expression load_imm_aux_expressions nth reference_control_expr_2312 eval_hfexpr_validif_policy eval_href_validif_policy]. rewrite S1;destruct (msb word);reflexivity. }
 destruct lane as [|lane].
 { cbn [Nat.add Nat.mul load_imm_aux_node load_imm_aux_ids nth] in S1. cbn [Nat.add Nat.mul load_imm_aux_expression load_imm_aux_expressions nth reference_control_expr_2316 eval_hfexpr_validif_policy eval_href_validif_policy]. rewrite S1;destruct (msb word);reflexivity. }
lia. }
 assert (S3 : VM.find (load_imm_aux_node (Nat.add 10 (Nat.mul 4 lane))) (history time) = Some (Gval (Fuint 32) (sext_to 32 word))).
 { eapply (load_imm_aux_value (Nat.add 10 (Nat.mul 4 lane)) inputs path history limit reset time);[lia|exact Resets|exact Steps|exact Lower|exact Upper|].
 intro site.
 destruct lane as [|lane].
 { cbn [Nat.add Nat.mul load_imm_aux_node load_imm_aux_ids nth] in S2. cbn [Nat.add Nat.mul load_imm_aux_expression load_imm_aux_expressions nth reference_control_expr_2301 eval_hfexpr_validif_policy eval_href_validif_policy]. rewrite S2 Low. unfold eval_binop. rewrite immediate_cat_no_absorbing. cbn. unfold sext_to,sext. rewrite Size. reflexivity. }
 destruct lane as [|lane].
 { cbn [Nat.add Nat.mul load_imm_aux_node load_imm_aux_ids nth] in S2. cbn [Nat.add Nat.mul load_imm_aux_expression load_imm_aux_expressions nth reference_control_expr_2305 eval_hfexpr_validif_policy eval_href_validif_policy]. rewrite S2 Low. unfold eval_binop. rewrite immediate_cat_no_absorbing. cbn. unfold sext_to,sext. rewrite Size. reflexivity. }
 destruct lane as [|lane].
 { cbn [Nat.add Nat.mul load_imm_aux_node load_imm_aux_ids nth] in S2. cbn [Nat.add Nat.mul load_imm_aux_expression load_imm_aux_expressions nth reference_control_expr_2309 eval_hfexpr_validif_policy eval_href_validif_policy]. rewrite S2 Low. unfold eval_binop. rewrite immediate_cat_no_absorbing. cbn. unfold sext_to,sext. rewrite Size. reflexivity. }
 destruct lane as [|lane].
 { cbn [Nat.add Nat.mul load_imm_aux_node load_imm_aux_ids nth] in S2. cbn [Nat.add Nat.mul load_imm_aux_expression load_imm_aux_expressions nth reference_control_expr_2313 eval_hfexpr_validif_policy eval_href_validif_policy]. rewrite S2 Low. unfold eval_binop. rewrite immediate_cat_no_absorbing. cbn. unfold sext_to,sext. rewrite Size. reflexivity. }
 destruct lane as [|lane].
 { cbn [Nat.add Nat.mul load_imm_aux_node load_imm_aux_ids nth] in S2. cbn [Nat.add Nat.mul load_imm_aux_expression load_imm_aux_expressions nth reference_control_expr_2317 eval_hfexpr_validif_policy eval_href_validif_policy]. rewrite S2 Low. unfold eval_binop. rewrite immediate_cat_no_absorbing. cbn. unfold sext_to,sext. rewrite Size. reflexivity. }
lia. }
 do 5 (destruct lane as [|lane];[exact S3|]);lia.
Qed.
Theorem reference_load_immediate_history inputs path history limit reset time instruction lane :
 (lane < 5)%coq_nat -> size instruction = 32%nat ->
 (forall t, (t <= limit)%coq_nat -> VM.find 1 (history t) = Some (Gval (Fuint 1) [::reset])) ->
 (forall t, (t < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history t) false (history t) flat_statements = Some (history (S t))) ->
 (forall t, (200 <= t)%coq_nat -> (t <= limit)%coq_nat -> VM.find 1884 (history t) = Some (Gval (Fuint 32) instruction)) ->
 (500 <= time)%coq_nat -> (time < limit)%coq_nat ->
 VM.find 1707 (history time) = Some (Gval (Fuint 1) [::true]) ->
 (forall upper n, (n < load_imm_mux_count upper)%coq_nat -> VM.find (load_imm_mux_guard upper n) (history time) = Some (Gval (Fuint 1) [::Nat.eqb n (Nat.sub 4 lane)])) ->
 VM.find 2552 (history time) = Some (Gval (Fuint 32) (load_i_immediate instruction)).
Proof.
 intros Lane Size Resets Steps Source Lower Upper Enabled Guards.
 pose proof (load_imm_low_history inputs path history limit reset time instruction lane Lane Size Resets Steps Source Lower Upper Enabled (Guards false)) as Low.
 assert (LowSize : size (drop 20 (take 32 instruction)) = 12%nat) by (rewrite size_drop size_take Size;reflexivity).
 pose proof (load_imm_sign_history inputs path history limit reset time (drop 20 (take 32 instruction)) lane Lane LowSize Resets Steps Lower Upper Low) as Sign.
 assert (Selected : VM.find 2550 (history time) = Some (Gval (Fuint 32) (load_i_immediate instruction))).
 { change (VM.find (load_imm_mux_node true 10) (history time) = Some (Gval (Fuint (load_imm_mux_width true)) (load_i_immediate instruction))).
   eapply (load_imm_mux_suffix_history true inputs path history limit reset time (Nat.sub 4 lane) (load_i_immediate instruction));[cbn [load_imm_mux_count];lia|exact (load_i_immediate_size instruction Size)|exact Resets|exact Steps| |exact Lower|exact Upper|exact (Guards true)|exact Sign|lia|cbn [load_imm_mux_count];lia].
   intros t L U. exists (Gval (Fuint 32) instruction);split;[apply Source;assumption|reflexivity]. }
 assert (EnabledValue : VM.find 2551 (history time) = Some (Gval (Fuint 32) (load_i_immediate instruction))).
 { eapply (load_imm_aux_value 27 inputs path history limit reset time);[lia|exact Resets|exact Steps|exact Lower|exact Upper|].
   intro site. cbn [load_imm_aux_expression load_imm_aux_expressions nth reference_control_expr_2551 eval_hfexpr_validif_policy eval_href_validif_policy].
   rewrite Enabled;cbn;rewrite Selected. change (adapt_hvalue_as_type (Gval (Fuint 32) (load_i_immediate instruction)) (Gtyp (Fuint 32)) = Some (Gval (Fuint 32) (load_i_immediate instruction))). apply dut_decode_adapt;exact (load_i_immediate_size instruction Size). }
 eapply (load_imm_aux_value 28 inputs path history limit reset time);[lia|exact Resets|exact Steps|exact Lower|exact Upper|].
 intro site. exact EnabledValue.
Qed.
Lemma load_imm_fence_false invalid s0 s1 s2 instruction lane :
 (lane < 5)%coq_nat -> load_type_is_load instruction lane ->
 VM.find 1884 s0 = Some (Gval (Fuint 32) instruction) ->
 formal_value_iter invalid flat_memories s0 false s0 flat_statements = Some s1 ->
 formal_value_iter invalid flat_memories s1 false s1 flat_statements = Some s2 ->
 VM.find 1929 s2 = Some (Gval (Fuint 1) [::false]).
Proof.
 intros Lane Load Instruction Step1 Step2.
 assert (Mask : VM.find 1928 s1 = Some (Gval (Fuint 32) (andB instruction (from_N 15 28799)))).
 { eapply (reference_redirect_ground_step reference_control_0_offsets reference_control_0_nodes 1928 reference_control_expr_1928);
 [exact reference_control_0_positions|exact reference_control_0_safety|exact reference_control_member_1928| |exact Step1].
 intro site. cbn [reference_control_expr_1928 eval_hfexpr_validif_policy eval_href_validif_policy]. rewrite Instruction. reflexivity. }
 eapply (reference_redirect_ground_step reference_control_0_offsets reference_control_0_nodes 1929 reference_control_expr_1929);
 [exact reference_control_0_positions|exact reference_control_0_safety|exact reference_control_member_1929| |exact Step2].
 intro site. cbn [reference_control_expr_1929 eval_hfexpr_validif_policy eval_href_validif_policy]. rewrite Mask.
 change (eval_binop (Bcomp Beq) (Gval (Fuint 4) (from_N 4 15)) (Gval (Fuint 32) (andB instruction (from_N 15 28799))) = Some (Gval (Fuint 1) [::false])).
 rewrite (redirect_mask_decode instruction (from_N 15 28799) (from_N 4 15) 32 15 4).
 change (Some (Gval (Fuint 1) [::N.eqb (N.land (to_N instruction) 28799) 15]) = Some (Gval (Fuint 1) [::false])).
 unfold load_type_is_load in Load. rewrite Load. do 5 (destruct lane as [|lane];[reflexivity|]);lia.
Qed.
Require Import JointUpdateBoundaryHistory.
Theorem reference_load_immediate_observed memory inputs k observed instruction lane :
 generated_observe memory inputs k = Some observed -> generated_legal_trace memory inputs k ->
 VM.find 1 (formal_external_inputs (generated_observation_input inputs k)) = Some (Gval (Fuint 1) [::false]) ->
 (lane < 5)%coq_nat -> VM.find 7750 (top_environment observed) = Some (Gval (Fuint 32) instruction) ->
 load_type_is_load instruction lane ->
 VM.find 2552 (top_environment observed) = Some (Gval (Fuint 32) (load_i_immediate instruction)).
Proof.
 intros Observe Legal Reset Lane Instruction Load.
 pose proof (proj2 (load_pipeline_load_reference_enabled memory inputs k observed instruction lane Observe Legal Reset Lane Instruction Load)) as Enabled.
 destruct (observed_joint_register_concrete memory inputs k observed 7750%nat 32%nat Observe Legal load_type_instruction_member) as [word [Size Word]].
 rewrite Instruction in Word. inversion Word;subst word.
 destruct (observed_history memory inputs k observed Observe Legal) as [reset [history [Last [Steps Resets]]]].
 assert (Inst : forall t, (t <= 9259)%coq_nat -> VM.find 7750 (history t) = Some (Gval (Fuint 32) instruction)).
 { intros t Upper. pose proof (joint_update_register_history_same _ history 9259 7750 32 load_type_instruction_member Steps) as Hold.
   rewrite (Hold t Upper). rewrite <- (Hold 9259%nat ltac:(lia)). rewrite Last. exact Instruction. }
 assert (Enable : forall t, (195 <= t)%coq_nat -> (t <= 9259)%coq_nat -> VM.find 1707 (history t) = Some (Gval (Fuint 1) [::true])).
 { intros t Lower Upper. rewrite (reference_control_stable_1707_history (generated_observation_input inputs k) nil history 9259 reset Resets Steps t 9259%nat ltac:(lia) ltac:(lia) Upper ltac:(lia)) Last. exact Enabled. }
 assert (Source : forall t, (200 <= t)%coq_nat -> (t <= 9259)%coq_nat -> VM.find 1884 (history t) = Some (Gval (Fuint 32) instruction)).
 { intros t Lower Upper. exact (memory_reference_instruction_history _ history 9259 195 instruction true Size Steps Inst Enable t Lower Upper). }
 assert (Guards : forall row, (row < 8)%coq_nat -> VM.find (reference_memory_guard row) (history 9250%nat) = Some (Gval (Fuint 1) [::Nat.eqb row lane])).
 { intros row Row. pose proof (memory_reference_decode_observed memory inputs k observed instruction true row Observe Legal Row Instruction Enabled) as G.
   cbn [memory_reference_instruction] in G. rewrite (reference_memory_decode_load (to_N instruction) lane row Lane Row Load) in G.
   assert (Stable : VM.find (reference_memory_guard row) (history 9250%nat) = VM.find (reference_memory_guard row) (history 9259%nat)).
   {
    destruct row as [|row];[apply (reference_control_stable_1886_history (generated_observation_input inputs k) nil history 9259 reset Resets Steps 9250 9259);vm_compute;lia|].
    destruct row as [|row];[apply (reference_control_stable_1958_history (generated_observation_input inputs k) nil history 9259 reset Resets Steps 9250 9259);vm_compute;lia|].
    destruct row as [|row];[apply (reference_control_stable_1962_history (generated_observation_input inputs k) nil history 9259 reset Resets Steps 9250 9259);vm_compute;lia|].
    destruct row as [|row];[apply (reference_control_stable_1966_history (generated_observation_input inputs k) nil history 9259 reset Resets Steps 9250 9259);vm_compute;lia|].
    destruct row as [|row];[apply (reference_control_stable_1970_history (generated_observation_input inputs k) nil history 9259 reset Resets Steps 9250 9259);vm_compute;lia|].
    destruct row as [|row];[apply (reference_control_stable_1951_history (generated_observation_input inputs k) nil history 9259 reset Resets Steps 9250 9259);vm_compute;lia|].
    destruct row as [|row];[apply (reference_control_stable_1946_history (generated_observation_input inputs k) nil history 9259 reset Resets Steps 9250 9259);vm_compute;lia|].
    destruct row as [|row];[apply (reference_control_stable_1941_history (generated_observation_input inputs k) nil history 9259 reset Resets Steps 9250 9259);vm_compute;lia|].
    lia. } rewrite Stable Last. exact G. }
 assert (Ecall : VM.find 1933 (history 9250%nat) = Some (Gval (Fuint 1) [::false])).
 { rewrite (reference_control_stable_1933_history (generated_observation_input inputs k) nil history 9259 reset Resets Steps 9250 9259 ltac:(vm_compute;lia) ltac:(vm_compute;lia) ltac:(vm_compute;lia) ltac:(vm_compute;lia)) Last.
   exact (reference_system_absent_observed memory inputs k observed instruction true false Observe Legal Reset Instruction Enabled). }
 assert (Ebreak : VM.find 1937 (history 9250%nat) = Some (Gval (Fuint 1) [::false])).
 { rewrite (reference_control_stable_1937_history (generated_observation_input inputs k) nil history 9259 reset Resets Steps 9250 9259 ltac:(vm_compute;lia) ltac:(vm_compute;lia) ltac:(vm_compute;lia) ltac:(vm_compute;lia)) Last.
   exact (reference_system_absent_observed memory inputs k observed instruction true true Observe Legal Reset Instruction Enabled). }
 assert (Fence : VM.find 1929 (history 9250%nat) = Some (Gval (Fuint 1) [::false])).
 { eapply (load_imm_fence_false _ (history 9248%nat) (history 9249%nat) (history 9250%nat) instruction lane Lane Load);[apply Source;vm_compute;lia|apply Steps;vm_compute;lia|apply Steps;vm_compute;lia]. }
 pose proof (reference_load_immediate_history (generated_observation_input inputs k) nil history 9259 reset 9250 instruction lane Lane Size Resets Steps Source ltac:(vm_compute;lia) ltac:(vm_compute;lia) (Enable 9250%nat ltac:(vm_compute;lia) ltac:(vm_compute;lia)) (load_imm_guards_selected (history 9250%nat) lane Lane Guards Fence Ecall Ebreak)) as Value.
 rewrite (reference_control_stable_2552_history (generated_observation_input inputs k) nil history 9259 reset Resets Steps 9250 9259 ltac:(vm_compute;lia) ltac:(vm_compute;lia) ltac:(vm_compute;lia) ltac:(vm_compute;lia)) Last in Value. exact Value.
Qed.
