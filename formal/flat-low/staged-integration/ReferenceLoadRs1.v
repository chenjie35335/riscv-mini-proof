Require Import ReferenceRegisterRead ReferenceRs1Types ReferenceLoadImmediate ReferenceImmediateTypes ReferenceInstructionDecode ReferenceControlStabilityHistory ReferenceControlNodeCongruence0 ReferenceControlNodeCertificates0 ReferenceControlExpressions ReferenceRedirectSpine CoreSocModel ComparisonNodes LoadTypeCorrespondence LoadImmediateSemantics RFReadPorts DUTRedirectDecode.
From Coq Require Import NArith List Lia PeanoNat.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From nbits Require Import NBits.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Firrtl_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Local Opaque flat_statements flat_memories generated_modules generated_top.
Definition reference_load_rs1_node n : VarOrder.T := N.of_nat(Nat.add 2125 n).
Definition reference_load_rs1_guard n := reference_instruction_guard(Nat.add 29 n).
Definition reference_load_rs1_yes n : VarOrder.T := nth 0 [::1972;1968;1964;1960;1956;1954;1949;1944;1939;1935;1931;1927;1922;1917;1912;1907;1902;1897;1892] n.
Definition reference_load_rs1_expression n := @Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T (reference_load_rs1_guard n))) (@Eref VarOrder.T (@Eid VarOrder.T (reference_load_rs1_yes n))) (@Eref VarOrder.T (@Eid VarOrder.T (match n with O=>2124 | S p=>reference_load_rs1_node p end))).
Lemma reference_load_rs1_member n : (n<19)%coq_nat ->List.In(reference_load_rs1_node n,reference_load_rs1_expression n)reference_control_0_nodes.
Proof. intro Bound.
 destruct n as [|n];[exact reference_control_member_2125|].
 destruct n as [|n];[exact reference_control_member_2126|].
 destruct n as [|n];[exact reference_control_member_2127|].
 destruct n as [|n];[exact reference_control_member_2128|].
 destruct n as [|n];[exact reference_control_member_2129|].
 destruct n as [|n];[exact reference_control_member_2130|].
 destruct n as [|n];[exact reference_control_member_2131|].
 destruct n as [|n];[exact reference_control_member_2132|].
 destruct n as [|n];[exact reference_control_member_2133|].
 destruct n as [|n];[exact reference_control_member_2134|].
 destruct n as [|n];[exact reference_control_member_2135|].
 destruct n as [|n];[exact reference_control_member_2136|].
 destruct n as [|n];[exact reference_control_member_2137|].
 destruct n as [|n];[exact reference_control_member_2138|].
 destruct n as [|n];[exact reference_control_member_2139|].
 destruct n as [|n];[exact reference_control_member_2140|].
 destruct n as [|n];[exact reference_control_member_2141|].
 destruct n as [|n];[exact reference_control_member_2142|].
 destruct n as [|n];[exact reference_control_member_2143|].
 lia. Qed.
Theorem reference_load_rs1_step n invalid old result word : (n<19)%coq_nat ->
 (forall site,eval_hfexpr_validif_policy(isolated_validif_policy invalid)site flat_memories(reference_load_rs1_expression n)old old=Some(Gval(Fuint 5)word)) ->
 formal_value_iter invalid flat_memories old false old flat_statements=Some result ->
 VM.find(reference_load_rs1_node n)result=Some(Gval(Fuint 5)word).
Proof. intros Bound Eval Step. eapply(reference_redirect_ground_step reference_control_0_offsets reference_control_0_nodes _ (reference_load_rs1_expression n));[exact reference_control_0_positions|exact reference_control_0_safety|apply reference_load_rs1_member;exact Bound|exact Eval|exact Step]. Qed.
Lemma reference_load_rs1_same n inputs path history limit reset time : (n<19)%coq_nat ->
 (forall t,(t<=limit)%coq_nat ->VM.find 1(history t)=Some(Gval(Fuint 1)[::reset])) ->
 (forall t,(t<limit)%coq_nat ->formal_value_iter(formal_invalid_policy inputs path)flat_memories(history t)false(history t)flat_statements=Some(history(S t))) ->
 (500<=time)%coq_nat ->(time<limit)%coq_nat ->
 VM.find(reference_load_rs1_node n)(history time)=VM.find(reference_load_rs1_node n)(history(S time)).
Proof. intros Bound Resets Steps Lower Upper.
 destruct n as [|n];[apply(reference_control_stable_2125_history inputs path history limit reset Resets Steps time (S time));lia|].
 destruct n as [|n];[apply(reference_control_stable_2126_history inputs path history limit reset Resets Steps time (S time));lia|].
 destruct n as [|n];[apply(reference_control_stable_2127_history inputs path history limit reset Resets Steps time (S time));lia|].
 destruct n as [|n];[apply(reference_control_stable_2128_history inputs path history limit reset Resets Steps time (S time));lia|].
 destruct n as [|n];[apply(reference_control_stable_2129_history inputs path history limit reset Resets Steps time (S time));lia|].
 destruct n as [|n];[apply(reference_control_stable_2130_history inputs path history limit reset Resets Steps time (S time));lia|].
 destruct n as [|n];[apply(reference_control_stable_2131_history inputs path history limit reset Resets Steps time (S time));lia|].
 destruct n as [|n];[apply(reference_control_stable_2132_history inputs path history limit reset Resets Steps time (S time));lia|].
 destruct n as [|n];[apply(reference_control_stable_2133_history inputs path history limit reset Resets Steps time (S time));lia|].
 destruct n as [|n];[apply(reference_control_stable_2134_history inputs path history limit reset Resets Steps time (S time));lia|].
 destruct n as [|n];[apply(reference_control_stable_2135_history inputs path history limit reset Resets Steps time (S time));lia|].
 destruct n as [|n];[apply(reference_control_stable_2136_history inputs path history limit reset Resets Steps time (S time));lia|].
 destruct n as [|n];[apply(reference_control_stable_2137_history inputs path history limit reset Resets Steps time (S time));lia|].
 destruct n as [|n];[apply(reference_control_stable_2138_history inputs path history limit reset Resets Steps time (S time));lia|].
 destruct n as [|n];[apply(reference_control_stable_2139_history inputs path history limit reset Resets Steps time (S time));lia|].
 destruct n as [|n];[apply(reference_control_stable_2140_history inputs path history limit reset Resets Steps time (S time));lia|].
 destruct n as [|n];[apply(reference_control_stable_2141_history inputs path history limit reset Resets Steps time (S time));lia|].
 destruct n as [|n];[apply(reference_control_stable_2142_history inputs path history limit reset Resets Steps time (S time));lia|].
 destruct n as [|n];[apply(reference_control_stable_2143_history inputs path history limit reset Resets Steps time (S time));lia|].
 lia. Qed.
Lemma reference_load_rs1_branch_types n invalid history limit time : (n<19)%coq_nat ->
 (forall t,(t<limit)%coq_nat ->formal_value_iter invalid flat_memories(history t)false(history t)flat_statements=Some(history(S t))) ->
 (forall t,(200<=t)%coq_nat ->(t<=limit)%coq_nat ->exists v,VM.find 1884(history t)=Some v /\ type_of_val v=Gtyp(Fuint 32)) ->
 (500<=time)%coq_nat ->(time<=limit)%coq_nat ->
 (exists v,VM.find(reference_load_rs1_yes n)(history time)=Some v /\type_of_val v=Gtyp(Fuint 5)) /\
 (exists v,VM.find(match n with O=>2124 | S p=>reference_load_rs1_node p end)(history time)=Some v /\type_of_val v=Gtyp(Fuint 5)).
Proof. intros Bound Steps Source Lower Upper.
 destruct n as [|n]. { split.
 - exact(reference_rs1_types_history invalid history limit 200 Steps Source 48%nat ltac:(vm_compute;lia) time ltac:(cbv [reference_rs1_rank reference_rs1_ranks nth];lia) Upper).
 - exact(reference_rs1_types_history invalid history limit 200 Steps Source 148%nat ltac:(vm_compute;lia) time ltac:(cbv [reference_rs1_rank reference_rs1_ranks nth];lia) Upper).
 }
 destruct n as [|n]. { split.
 - exact(reference_rs1_types_history invalid history limit 200 Steps Source 46%nat ltac:(vm_compute;lia) time ltac:(cbv [reference_rs1_rank reference_rs1_ranks nth];lia) Upper).
 - exact(reference_rs1_types_history invalid history limit 200 Steps Source 149%nat ltac:(vm_compute;lia) time ltac:(cbv [reference_rs1_rank reference_rs1_ranks nth];lia) Upper).
 }
 destruct n as [|n]. { split.
 - exact(reference_rs1_types_history invalid history limit 200 Steps Source 44%nat ltac:(vm_compute;lia) time ltac:(cbv [reference_rs1_rank reference_rs1_ranks nth];lia) Upper).
 - exact(reference_rs1_types_history invalid history limit 200 Steps Source 150%nat ltac:(vm_compute;lia) time ltac:(cbv [reference_rs1_rank reference_rs1_ranks nth];lia) Upper).
 }
 destruct n as [|n]. { split.
 - exact(reference_rs1_types_history invalid history limit 200 Steps Source 42%nat ltac:(vm_compute;lia) time ltac:(cbv [reference_rs1_rank reference_rs1_ranks nth];lia) Upper).
 - exact(reference_rs1_types_history invalid history limit 200 Steps Source 151%nat ltac:(vm_compute;lia) time ltac:(cbv [reference_rs1_rank reference_rs1_ranks nth];lia) Upper).
 }
 destruct n as [|n]. { split.
 - exact(reference_rs1_types_history invalid history limit 200 Steps Source 40%nat ltac:(vm_compute;lia) time ltac:(cbv [reference_rs1_rank reference_rs1_ranks nth];lia) Upper).
 - exact(reference_rs1_types_history invalid history limit 200 Steps Source 152%nat ltac:(vm_compute;lia) time ltac:(cbv [reference_rs1_rank reference_rs1_ranks nth];lia) Upper).
 }
 destruct n as [|n]. { split.
 - exact(reference_rs1_types_history invalid history limit 200 Steps Source 38%nat ltac:(vm_compute;lia) time ltac:(cbv [reference_rs1_rank reference_rs1_ranks nth];lia) Upper).
 - exact(reference_rs1_types_history invalid history limit 200 Steps Source 153%nat ltac:(vm_compute;lia) time ltac:(cbv [reference_rs1_rank reference_rs1_ranks nth];lia) Upper).
 }
 destruct n as [|n]. { split.
 - exact(reference_rs1_types_history invalid history limit 200 Steps Source 35%nat ltac:(vm_compute;lia) time ltac:(cbv [reference_rs1_rank reference_rs1_ranks nth];lia) Upper).
 - exact(reference_rs1_types_history invalid history limit 200 Steps Source 154%nat ltac:(vm_compute;lia) time ltac:(cbv [reference_rs1_rank reference_rs1_ranks nth];lia) Upper).
 }
 destruct n as [|n]. { split.
 - exact(reference_rs1_types_history invalid history limit 200 Steps Source 32%nat ltac:(vm_compute;lia) time ltac:(cbv [reference_rs1_rank reference_rs1_ranks nth];lia) Upper).
 - exact(reference_rs1_types_history invalid history limit 200 Steps Source 155%nat ltac:(vm_compute;lia) time ltac:(cbv [reference_rs1_rank reference_rs1_ranks nth];lia) Upper).
 }
 destruct n as [|n]. { split.
 - exact(reference_rs1_types_history invalid history limit 200 Steps Source 29%nat ltac:(vm_compute;lia) time ltac:(cbv [reference_rs1_rank reference_rs1_ranks nth];lia) Upper).
 - exact(reference_rs1_types_history invalid history limit 200 Steps Source 156%nat ltac:(vm_compute;lia) time ltac:(cbv [reference_rs1_rank reference_rs1_ranks nth];lia) Upper).
 }
 destruct n as [|n]. { split.
 - exact(reference_rs1_types_history invalid history limit 200 Steps Source 27%nat ltac:(vm_compute;lia) time ltac:(cbv [reference_rs1_rank reference_rs1_ranks nth];lia) Upper).
 - exact(reference_rs1_types_history invalid history limit 200 Steps Source 157%nat ltac:(vm_compute;lia) time ltac:(cbv [reference_rs1_rank reference_rs1_ranks nth];lia) Upper).
 }
 destruct n as [|n]. { split.
 - exact(reference_rs1_types_history invalid history limit 200 Steps Source 25%nat ltac:(vm_compute;lia) time ltac:(cbv [reference_rs1_rank reference_rs1_ranks nth];lia) Upper).
 - exact(reference_rs1_types_history invalid history limit 200 Steps Source 158%nat ltac:(vm_compute;lia) time ltac:(cbv [reference_rs1_rank reference_rs1_ranks nth];lia) Upper).
 }
 destruct n as [|n]. { split.
 - exact(reference_rs1_types_history invalid history limit 200 Steps Source 23%nat ltac:(vm_compute;lia) time ltac:(cbv [reference_rs1_rank reference_rs1_ranks nth];lia) Upper).
 - exact(reference_rs1_types_history invalid history limit 200 Steps Source 159%nat ltac:(vm_compute;lia) time ltac:(cbv [reference_rs1_rank reference_rs1_ranks nth];lia) Upper).
 }
 destruct n as [|n]. { split.
 - exact(reference_rs1_types_history invalid history limit 200 Steps Source 20%nat ltac:(vm_compute;lia) time ltac:(cbv [reference_rs1_rank reference_rs1_ranks nth];lia) Upper).
 - exact(reference_rs1_types_history invalid history limit 200 Steps Source 160%nat ltac:(vm_compute;lia) time ltac:(cbv [reference_rs1_rank reference_rs1_ranks nth];lia) Upper).
 }
 destruct n as [|n]. { split.
 - exact(reference_rs1_types_history invalid history limit 200 Steps Source 17%nat ltac:(vm_compute;lia) time ltac:(cbv [reference_rs1_rank reference_rs1_ranks nth];lia) Upper).
 - exact(reference_rs1_types_history invalid history limit 200 Steps Source 161%nat ltac:(vm_compute;lia) time ltac:(cbv [reference_rs1_rank reference_rs1_ranks nth];lia) Upper).
 }
 destruct n as [|n]. { split.
 - exact(reference_rs1_types_history invalid history limit 200 Steps Source 14%nat ltac:(vm_compute;lia) time ltac:(cbv [reference_rs1_rank reference_rs1_ranks nth];lia) Upper).
 - exact(reference_rs1_types_history invalid history limit 200 Steps Source 162%nat ltac:(vm_compute;lia) time ltac:(cbv [reference_rs1_rank reference_rs1_ranks nth];lia) Upper).
 }
 destruct n as [|n]. { split.
 - exact(reference_rs1_types_history invalid history limit 200 Steps Source 11%nat ltac:(vm_compute;lia) time ltac:(cbv [reference_rs1_rank reference_rs1_ranks nth];lia) Upper).
 - exact(reference_rs1_types_history invalid history limit 200 Steps Source 163%nat ltac:(vm_compute;lia) time ltac:(cbv [reference_rs1_rank reference_rs1_ranks nth];lia) Upper).
 }
 destruct n as [|n]. { split.
 - exact(reference_rs1_types_history invalid history limit 200 Steps Source 8%nat ltac:(vm_compute;lia) time ltac:(cbv [reference_rs1_rank reference_rs1_ranks nth];lia) Upper).
 - exact(reference_rs1_types_history invalid history limit 200 Steps Source 164%nat ltac:(vm_compute;lia) time ltac:(cbv [reference_rs1_rank reference_rs1_ranks nth];lia) Upper).
 }
 destruct n as [|n]. { split.
 - exact(reference_rs1_types_history invalid history limit 200 Steps Source 5%nat ltac:(vm_compute;lia) time ltac:(cbv [reference_rs1_rank reference_rs1_ranks nth];lia) Upper).
 - exact(reference_rs1_types_history invalid history limit 200 Steps Source 165%nat ltac:(vm_compute;lia) time ltac:(cbv [reference_rs1_rank reference_rs1_ranks nth];lia) Upper).
 }
 destruct n as [|n]. { split.
 - exact(reference_rs1_types_history invalid history limit 200 Steps Source 2%nat ltac:(vm_compute;lia) time ltac:(cbv [reference_rs1_rank reference_rs1_ranks nth];lia) Upper).
 - exact(reference_rs1_types_history invalid history limit 200 Steps Source 166%nat ltac:(vm_compute;lia) time ltac:(cbv [reference_rs1_rank reference_rs1_ranks nth];lia) Upper).
 }
 lia. Qed.
Definition reference_load_rs1_aux_ids : seq VarOrder.T := [::1955;1956;1959;1960;1963;1964;1967;1968;1971;1972;2144;2145].
Definition reference_load_rs1_aux_node i := nth 0 reference_load_rs1_aux_ids i.
Definition reference_load_rs1_aux_expressions := [::reference_control_expr_1955;reference_control_expr_1956;reference_control_expr_1959;reference_control_expr_1960;reference_control_expr_1963;reference_control_expr_1964;reference_control_expr_1967;reference_control_expr_1968;reference_control_expr_1971;reference_control_expr_1972;reference_control_expr_2144;reference_control_expr_2145].
Definition reference_load_rs1_aux_expression i := nth (@Econst VarOrder.T (Fuint 1)[::false]) reference_load_rs1_aux_expressions i.
Lemma reference_load_rs1_aux_member i : (i<12)%coq_nat ->List.In(reference_load_rs1_aux_node i,reference_load_rs1_aux_expression i)reference_control_0_nodes.
Proof. intro Bound.
 destruct i as [|i];[exact reference_control_member_1955|].
 destruct i as [|i];[exact reference_control_member_1956|].
 destruct i as [|i];[exact reference_control_member_1959|].
 destruct i as [|i];[exact reference_control_member_1960|].
 destruct i as [|i];[exact reference_control_member_1963|].
 destruct i as [|i];[exact reference_control_member_1964|].
 destruct i as [|i];[exact reference_control_member_1967|].
 destruct i as [|i];[exact reference_control_member_1968|].
 destruct i as [|i];[exact reference_control_member_1971|].
 destruct i as [|i];[exact reference_control_member_1972|].
 destruct i as [|i];[exact reference_control_member_2144|].
 destruct i as [|i];[exact reference_control_member_2145|].
 lia. Qed.
Lemma reference_load_rs1_aux_value i inputs path history limit reset time width word : (i<12)%coq_nat ->
 (forall t,(t<=limit)%coq_nat ->VM.find 1(history t)=Some(Gval(Fuint 1)[::reset])) ->
 (forall t,(t<limit)%coq_nat ->formal_value_iter(formal_invalid_policy inputs path)flat_memories(history t)false(history t)flat_statements=Some(history(S t))) ->
 (500<=time)%coq_nat ->(time<limit)%coq_nat ->
 (forall site,eval_hfexpr_validif_policy(isolated_validif_policy(formal_invalid_policy inputs path))site flat_memories(reference_load_rs1_aux_expression i)(history time)(history time)=Some(Gval(Fuint width)word)) ->
 VM.find(reference_load_rs1_aux_node i)(history time)=Some(Gval(Fuint width)word).
Proof. intros Bound Resets Steps Lower Upper Eval.
 assert(Stable:VM.find(reference_load_rs1_aux_node i)(history time)=VM.find(reference_load_rs1_aux_node i)(history(S time))). {
 destruct i as [|i];[apply(reference_control_stable_1955_history inputs path history limit reset Resets Steps time (S time));lia|].
 destruct i as [|i];[apply(reference_control_stable_1956_history inputs path history limit reset Resets Steps time (S time));lia|].
 destruct i as [|i];[apply(reference_control_stable_1959_history inputs path history limit reset Resets Steps time (S time));lia|].
 destruct i as [|i];[apply(reference_control_stable_1960_history inputs path history limit reset Resets Steps time (S time));lia|].
 destruct i as [|i];[apply(reference_control_stable_1963_history inputs path history limit reset Resets Steps time (S time));lia|].
 destruct i as [|i];[apply(reference_control_stable_1964_history inputs path history limit reset Resets Steps time (S time));lia|].
 destruct i as [|i];[apply(reference_control_stable_1967_history inputs path history limit reset Resets Steps time (S time));lia|].
 destruct i as [|i];[apply(reference_control_stable_1968_history inputs path history limit reset Resets Steps time (S time));lia|].
 destruct i as [|i];[apply(reference_control_stable_1971_history inputs path history limit reset Resets Steps time (S time));lia|].
 destruct i as [|i];[apply(reference_control_stable_1972_history inputs path history limit reset Resets Steps time (S time));lia|].
 destruct i as [|i];[apply(reference_control_stable_2144_history inputs path history limit reset Resets Steps time (S time));lia|].
 destruct i as [|i];[apply(reference_control_stable_2145_history inputs path history limit reset Resets Steps time (S time));lia|].
 lia. } rewrite Stable. eapply(reference_redirect_ground_step reference_control_0_offsets reference_control_0_nodes _ (reference_load_rs1_aux_expression i));[exact reference_control_0_positions|exact reference_control_0_safety|apply reference_load_rs1_aux_member;exact Bound|exact Eval|apply Steps;exact Upper]. Qed.
(* Actual load rs1 semantics. *)
Lemma reference_load_rs1_raw inputs path history limit reset time instruction lane :
 (lane<5)%coq_nat ->
 (forall t,(t<=limit)%coq_nat ->VM.find 1(history t)=Some(Gval(Fuint 1)[::reset])) ->
 (forall t,(t<limit)%coq_nat ->formal_value_iter(formal_invalid_policy inputs path)flat_memories(history t)false(history t)flat_statements=Some(history(S t))) ->
 (500<=time)%coq_nat ->(time<limit)%coq_nat ->
 VM.find 1884(history time)=Some(Gval(Fuint 32)instruction) ->
 VM.find(reference_load_rs1_yes(Nat.sub 4 lane))(history time)=Some(Gval(Fuint 5)(rf_instruction_address false instruction)).
Proof.
 intros Lane Resets Steps Lower Upper Source.
 assert (Raw : VM.find(reference_load_rs1_aux_node(Nat.mul 2 lane))(history time)=Some(Gval(Fuint 20)(take 20 instruction))).
 { eapply(reference_load_rs1_aux_value (Nat.mul 2 lane) inputs path history limit reset time);[lia|exact Resets|exact Steps|exact Lower|exact Upper|]. intro site.
 do 5 (destruct lane as [|lane];[cbn [Nat.add Nat.mul reference_load_rs1_aux_node reference_load_rs1_aux_expression reference_load_rs1_aux_expressions nth reference_control_expr_1955 reference_control_expr_1959 reference_control_expr_1963 reference_control_expr_1967 reference_control_expr_1971 eval_hfexpr_validif_policy eval_href_validif_policy];rewrite Source;cbn [eval_unop];rewrite drop0;reflexivity|]);lia. }
 assert (Slice : VM.find(reference_load_rs1_aux_node(S(Nat.mul 2 lane)))(history time)=Some(Gval(Fuint 5)(rf_instruction_address false instruction))).
 { eapply(reference_load_rs1_aux_value (S(Nat.mul 2 lane)) inputs path history limit reset time);[lia|exact Resets|exact Steps|exact Lower|exact Upper|]. intro site.
 do 5 (destruct lane as [|lane];[cbn [Nat.add Nat.mul reference_load_rs1_aux_node reference_load_rs1_aux_ids nth] in Raw;cbn [Nat.add Nat.mul reference_load_rs1_aux_expression reference_load_rs1_aux_expressions nth reference_control_expr_1956 reference_control_expr_1960 reference_control_expr_1964 reference_control_expr_1968 reference_control_expr_1972 eval_hfexpr_validif_policy eval_href_validif_policy];rewrite Raw;cbn [eval_unop];unfold rf_instruction_address;rewrite take_take;reflexivity|]);lia. }
 do 5 (destruct lane as [|lane];[exact Slice|]);lia.
Qed.
Theorem reference_load_rs1_history inputs path history limit reset time instruction lane :
 (lane<5)%coq_nat ->size instruction=32%nat ->
 (forall t,(t<=limit)%coq_nat ->VM.find 1(history t)=Some(Gval(Fuint 1)[::reset])) ->
 (forall t,(t<limit)%coq_nat ->formal_value_iter(formal_invalid_policy inputs path)flat_memories(history t)false(history t)flat_statements=Some(history(S t))) ->
 (forall t,(200<=t)%coq_nat ->(t<=limit)%coq_nat ->VM.find 1884(history t)=Some(Gval(Fuint 32)instruction)) ->
 (500<=time)%coq_nat ->(time<limit)%coq_nat ->
 VM.find 1707(history time)=Some(Gval(Fuint 1)[::true]) ->
 (forall n,(n<19)%coq_nat ->VM.find(reference_load_rs1_guard n)(history time)=Some(Gval(Fuint 1)[::Nat.eqb n(Nat.sub 4 lane)])) ->
 VM.find 2145(history time)=Some(Gval(Fuint 5)(rf_instruction_address false instruction)).
Proof.
 intros Lane Size Resets Steps Source Lower Upper Enabled Guards.
 assert (TypedSource : forall t,(200<=t)%coq_nat ->(t<=limit)%coq_nat ->exists v,VM.find 1884(history t)=Some v /\type_of_val v=Gtyp(Fuint 32)).
 { intros t L U. exists(Gval(Fuint 32)instruction);split;[apply Source;assumption|reflexivity]. }
 pose proof(reference_load_rs1_raw inputs path history limit reset time instruction lane Lane Resets Steps Lower Upper (Source time ltac:(lia)ltac:(lia))) as Raw.
 assert (Selected : VM.find 2143(history time)=Some(Gval(Fuint 5)(rf_instruction_address false instruction))).
 { change (VM.find(reference_load_rs1_node 18)(history time)=Some(Gval(Fuint 5)(rf_instruction_address false instruction))).
 eapply(immediate_stable_mux_suffix (formal_invalid_policy inputs path)(history time)(history(S time)) 19 (Nat.sub 4 lane) 5 (rf_instruction_address false instruction) 2124 reference_load_rs1_node reference_load_rs1_guard reference_load_rs1_yes);[lia|exact(rf_instruction_address_size false instruction Size)| | |exact Guards| | |exact Raw|lia|lia].
 - intros n Bound. exact(reference_load_rs1_same n inputs path history limit reset time Bound Resets Steps Lower Upper).
 - intros n Bound value Eval. apply(reference_load_rs1_step n _ _ _ value Bound Eval);apply Steps;exact Upper.
 - intros n Bound. exact(proj1(reference_load_rs1_branch_types n _ history limit time Bound Steps TypedSource Lower ltac:(lia))).
 - intros n Bound. exact(proj2(reference_load_rs1_branch_types n _ history limit time Bound Steps TypedSource Lower ltac:(lia))). }
 assert (Gate : VM.find 2144(history time)=Some(Gval(Fuint 5)(rf_instruction_address false instruction))).
 { eapply(reference_load_rs1_aux_value 10 inputs path history limit reset time);[lia|exact Resets|exact Steps|exact Lower|exact Upper|]. intro site.
 cbn [reference_load_rs1_aux_expression reference_load_rs1_aux_expressions nth reference_control_expr_2144 eval_hfexpr_validif_policy eval_href_validif_policy]. rewrite Enabled;cbn;rewrite Selected. apply dut_decode_adapt;exact(rf_instruction_address_size false instruction Size). }
 eapply(reference_load_rs1_aux_value 11 inputs path history limit reset time);[lia|exact Resets|exact Steps|exact Lower|exact Upper|]. intro site;exact Gate.
Qed.
Lemma reference_load_rs1_other n : (5<=n)%coq_nat ->(n<19)%coq_nat ->
 N.land(reference_instruction_mask(Nat.add 29 n))127=127 /\ N.land(reference_instruction_code(Nat.add 29 n))127<>3.
Proof. intros Lower Upper. do 19 (destruct n as [|n];[first[lia|vm_compute;split;[reflexivity|discriminate]]|]);lia. Qed.
Lemma reference_load_rs1_decode instruction lane n : (lane<5)%coq_nat ->(n<19)%coq_nat ->load_type_is_load instruction lane ->
 N.eqb(reference_instruction_code(Nat.add 29 n))(N.land(to_N instruction)(reference_instruction_mask(Nat.add 29 n)))=Nat.eqb n(Nat.sub 4 lane).
Proof.
 intros Lane Bound Load.
 assert (Opcode : N.land(to_N instruction)127=3).
 { pose proof(load_type_mask_projection (to_N instruction)28799(load_type_lane_code lane)ltac:(reflexivity)Load)as P. rewrite P. do 5 (destruct lane as [|lane];[reflexivity|]);lia. }
 destruct(Nat.lt_ge_cases n 5)as[Small|Large].
 - do 5 (destruct n as [|n];[cbn [Nat.add reference_instruction_mask reference_instruction_masks nth];unfold load_type_is_load in Load;rewrite Load;do 5 (destruct lane as [|lane];[reflexivity|]);lia|]);lia.
 - rewrite(proj2(Nat.eqb_neq n(Nat.sub 4 lane))ltac:(lia)). apply N.eqb_neq. intro Match.
   destruct(reference_load_rs1_other n Large Bound)as[Mask Different].
   pose proof(load_type_mask_projection (to_N instruction) _ _ Mask (Logic.eq_sym Match))as P. rewrite Opcode in P. apply Different;symmetry;exact P.
Qed.
Require Import LoadPipelineClassification MemoryRequestObservedSemantics FormalObservedHistory ObservedJointRegisterConcrete JointUpdateBoundaryHistory FormalLocalHistory.
Theorem reference_load_rs1_observed memory inputs k observed instruction lane :
 generated_observe memory inputs k = Some observed -> generated_legal_trace memory inputs k ->
 VM.find 1 (formal_external_inputs (generated_observation_input inputs k)) = Some (Gval (Fuint 1) [::false]) ->
 (lane < 5)%coq_nat -> VM.find 7750 (top_environment observed) = Some (Gval (Fuint 32) instruction) ->
 load_type_is_load instruction lane ->
 VM.find 2145 (top_environment observed) = Some (Gval (Fuint 5) (rf_instruction_address false instruction)).
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
 assert (Guards : forall n,(n<19)%coq_nat ->VM.find(reference_load_rs1_guard n)(history 9250%nat)=Some(Gval(Fuint 1)[::Nat.eqb n(Nat.sub 4 lane)])).
 { intros n Bound.
   set (h := fun t:nat => history (match t with O=>9248%nat | S O=>9249%nat | _=>9250%nat end)).
   assert (HS : forall t,(t<2)%coq_nat ->formal_value_iter(formal_invalid_policy(generated_observation_input inputs k)nil)flat_memories(h t)false(h t)flat_statements=Some(h(S t))).
   { intros [|[|t]] T;[apply Steps;vm_compute;lia|apply Steps;vm_compute;lia|lia]. }
   assert (HI : forall t,(t<=2)%coq_nat ->VM.find 1884(h t)=Some(Gval(Fuint 32)instruction)).
   { intros [|[|t]] T;unfold h;apply Source;vm_compute;lia. }
   pose proof(reference_instruction_decode_history _ h 2 instruction (Nat.add 29 n) ltac:(lia) HS HI 2 ltac:(lia) ltac:(lia))as Decode.
   rewrite(reference_load_rs1_decode instruction lane n Lane Bound Load)in Decode. exact Decode. }
 pose proof(reference_load_rs1_history (generated_observation_input inputs k)nil history 9259 reset 9250 instruction lane Lane Size Resets Steps Source ltac:(vm_compute;lia)ltac:(vm_compute;lia)(Enable 9250%nat ltac:(vm_compute;lia)ltac:(vm_compute;lia))Guards)as Value.
 rewrite(reference_control_stable_2145_history (generated_observation_input inputs k)nil history 9259 reset Resets Steps 9250 9259 ltac:(vm_compute;lia)ltac:(vm_compute;lia)ltac:(vm_compute;lia)ltac:(vm_compute;lia))Last in Value. exact Value.
Qed.
Require Import RFReferenceNopHistory RFArchitecturalRelation StagedRegisterHold.
Theorem reference_register_read_observed memory inputs k observed bank address :
 generated_observe memory inputs k=Some observed ->generated_legal_trace memory inputs k ->
 rf_reference_bank_at(top_environment observed)bank ->size address=5%nat ->
 VM.find 2145(top_environment observed)=Some(Gval(Fuint 5)address) ->
 VM.find 2209(top_environment observed)=Some(Gval(Fuint 32)(bank(to_nat address))).
Proof.
 intros Observe Legal Bank Size Address.
 destruct(observed_history memory inputs k observed Observe Legal)as[reset[history[Last[Steps Resets]]]].
 assert(Hold:forall t index,(t<=9259)%coq_nat ->(index<32)%coq_nat ->VM.find(N.of_nat(7299+index)%nat)(history t)=VM.find(N.of_nat(7299+index)%nat)(history 0%nat)).
 { intros t. induction t as[|t IH];intros index Time Index;[reflexivity|].
   destruct(rf_architectural_register_properties _ (rf_reference_register_member index Index))as[Present Rest].
   rewrite(staged_combinational_holds_registers _ flat_memories(history t)(history t)(history(S t))flat_statements _ Present (Steps t ltac:(lia))).
   apply IH;lia. }
 assert(Bank0:rf_reference_bank_at(history 0%nat)bank).
 { intros index Index. destruct(Bank index Index)as[W V];split;[exact W|].
   rewrite <-(Hold 9259%nat index ltac:(lia) Index). rewrite Last;exact V. }
 assert(Addr:forall t,(500<=t)%coq_nat ->(t<=9259)%coq_nat ->VM.find 2145(history t)=Some(Gval(Fuint 5)address)).
 { intros t Lower Upper. rewrite(reference_control_stable_2145_history (generated_observation_input inputs k)nil history 9259 reset Resets Steps t 9259 ltac:(lia)ltac:(vm_compute;lia)Upper ltac:(vm_compute;lia))Last;exact Address. }
 pose proof(reference_register_read_history (generated_observation_input inputs k)nil history 9259 500 bank address Bank0 Size ltac:(lia) Steps Addr 9259 ltac:(vm_compute;lia)ltac:(vm_compute;lia))as Value.
 rewrite Last in Value;exact Value.
Qed.
Theorem reference_load_rs1_bank_observed memory inputs k observed instruction lane bank :
 generated_observe memory inputs k=Some observed ->generated_legal_trace memory inputs k ->
 VM.find 1(formal_external_inputs(generated_observation_input inputs k))=Some(Gval(Fuint 1)[::false]) ->
 (lane<5)%coq_nat ->VM.find 7750(top_environment observed)=Some(Gval(Fuint 32)instruction) ->load_type_is_load instruction lane ->
 rf_reference_bank_at(top_environment observed)bank ->
 VM.find 2209(top_environment observed)=Some(Gval(Fuint 32)(bank(to_nat(rf_instruction_address false instruction)))).
Proof.
 intros Observe Legal Reset Lane Instruction Load Bank.
 assert(Size:size instruction=32%nat).
 { destruct(observed_joint_register_concrete memory inputs k observed 7750%nat 32%nat Observe Legal load_type_instruction_member)as[word[W V]]. rewrite Instruction in V;inversion V;subst;exact W. }
 eapply(reference_register_read_observed memory inputs k observed bank (rf_instruction_address false instruction));[exact Observe|exact Legal|exact Bank|exact(rf_instruction_address_size false instruction Size)|].
 exact(reference_load_rs1_observed memory inputs k observed instruction lane Observe Legal Reset Lane Instruction Load).
Qed.
