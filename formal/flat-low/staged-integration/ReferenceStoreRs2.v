Require Import ReferenceSecondRegisterRead ReferenceRs2Types ReferenceLoadImmediate ReferenceImmediateTypes ReferenceInstructionDecode ReferenceControlStabilityHistory ReferenceControlNodeCongruence0 ReferenceControlNodeCertificates0 ReferenceControlNodeCongruence2 ReferenceControlNodeCertificates2 ReferenceControlExpressions ReferenceRedirectSpine CoreSocModel ComparisonNodes LoadTypeCorrespondence LoadImmediateSemantics RFReadPorts DUTRedirectDecode.
From Coq Require Import NArith List Lia PeanoNat.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From nbits Require Import NBits.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Firrtl_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Local Opaque flat_statements flat_memories generated_modules generated_top.
Definition reference_store_rs2_node n : VarOrder.T := N.of_nat(Nat.add 2610 n).
Definition reference_store_rs2_decoder n := nth 0%nat [::34%nat;35%nat;36%nat;40%nat;41%nat;42%nat;43%nat;44%nat;45%nat;46%nat;47%nat] n.
Definition reference_store_rs2_guard n := reference_instruction_guard(reference_store_rs2_decoder n).
Definition reference_store_rs2_yes n : VarOrder.T := nth 0 [::2577;2576;2575;2574;2573;2572;2571;2570;2569;2568;2567] n.
Definition reference_store_rs2_expression n := @Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T (reference_store_rs2_guard n))) (@Eref VarOrder.T (@Eid VarOrder.T (reference_store_rs2_yes n))) (@Eref VarOrder.T (@Eid VarOrder.T (match n with O=>2609 | S p=>reference_store_rs2_node p end))).
Lemma reference_store_rs2_member n : (n<11)%coq_nat ->List.In(reference_store_rs2_node n,reference_store_rs2_expression n)reference_control_2_nodes.
Proof. intro Bound.
 destruct n as [|n];[exact reference_control_member_2610|].
 destruct n as [|n];[exact reference_control_member_2611|].
 destruct n as [|n];[exact reference_control_member_2612|].
 destruct n as [|n];[exact reference_control_member_2613|].
 destruct n as [|n];[exact reference_control_member_2614|].
 destruct n as [|n];[exact reference_control_member_2615|].
 destruct n as [|n];[exact reference_control_member_2616|].
 destruct n as [|n];[exact reference_control_member_2617|].
 destruct n as [|n];[exact reference_control_member_2618|].
 destruct n as [|n];[exact reference_control_member_2619|].
 destruct n as [|n];[exact reference_control_member_2620|].
 lia. Qed.
Theorem reference_store_rs2_step n invalid old result word : (n<11)%coq_nat ->
 (forall site,eval_hfexpr_validif_policy(isolated_validif_policy invalid)site flat_memories(reference_store_rs2_expression n)old old=Some(Gval(Fuint 5)word)) ->
 formal_value_iter invalid flat_memories old false old flat_statements=Some result ->
 VM.find(reference_store_rs2_node n)result=Some(Gval(Fuint 5)word).
Proof. intros Bound Eval Step. eapply(reference_redirect_ground_step reference_control_2_offsets reference_control_2_nodes _ (reference_store_rs2_expression n));[exact reference_control_2_positions|exact reference_control_2_safety|apply reference_store_rs2_member;exact Bound|exact Eval|exact Step]. Qed.
Lemma reference_store_rs2_same n inputs path history limit reset time : (n<11)%coq_nat ->
 (forall t,(t<=limit)%coq_nat ->VM.find 1(history t)=Some(Gval(Fuint 1)[::reset])) ->
 (forall t,(t<limit)%coq_nat ->formal_value_iter(formal_invalid_policy inputs path)flat_memories(history t)false(history t)flat_statements=Some(history(S t))) ->
 (500<=time)%coq_nat ->(time<limit)%coq_nat ->
 VM.find(reference_store_rs2_node n)(history time)=VM.find(reference_store_rs2_node n)(history(S time)).
Proof. intros Bound Resets Steps Lower Upper.
 destruct n as [|n];[apply(reference_control_stable_2610_history inputs path history limit reset Resets Steps time (S time));lia|].
 destruct n as [|n];[apply(reference_control_stable_2611_history inputs path history limit reset Resets Steps time (S time));lia|].
 destruct n as [|n];[apply(reference_control_stable_2612_history inputs path history limit reset Resets Steps time (S time));lia|].
 destruct n as [|n];[apply(reference_control_stable_2613_history inputs path history limit reset Resets Steps time (S time));lia|].
 destruct n as [|n];[apply(reference_control_stable_2614_history inputs path history limit reset Resets Steps time (S time));lia|].
 destruct n as [|n];[apply(reference_control_stable_2615_history inputs path history limit reset Resets Steps time (S time));lia|].
 destruct n as [|n];[apply(reference_control_stable_2616_history inputs path history limit reset Resets Steps time (S time));lia|].
 destruct n as [|n];[apply(reference_control_stable_2617_history inputs path history limit reset Resets Steps time (S time));lia|].
 destruct n as [|n];[apply(reference_control_stable_2618_history inputs path history limit reset Resets Steps time (S time));lia|].
 destruct n as [|n];[apply(reference_control_stable_2619_history inputs path history limit reset Resets Steps time (S time));lia|].
 destruct n as [|n];[apply(reference_control_stable_2620_history inputs path history limit reset Resets Steps time (S time));lia|].
 lia. Qed.
Lemma reference_store_rs2_branch_types n invalid history limit time : (n<11)%coq_nat ->
 (forall t,(t<limit)%coq_nat ->formal_value_iter invalid flat_memories(history t)false(history t)flat_statements=Some(history(S t))) ->
 (forall t,(200<=t)%coq_nat ->(t<=limit)%coq_nat ->exists v,VM.find 1884(history t)=Some v /\ type_of_val v=Gtyp(Fuint 32)) ->
 (500<=time)%coq_nat ->(time<=limit)%coq_nat ->
 (exists v,VM.find(reference_store_rs2_yes n)(history time)=Some v /\type_of_val v=Gtyp(Fuint 5)) /\
 (exists v,VM.find(match n with O=>2609 | S p=>reference_store_rs2_node p end)(history time)=Some v /\type_of_val v=Gtyp(Fuint 5)).
Proof. intros Bound Steps Source Lower Upper.
 destruct n as [|n]. { split.
 - exact(reference_rs2_types_history invalid history limit 200 Steps Source 43%nat ltac:(vm_compute;lia) time ltac:(cbv [reference_rs2_rank reference_rs2_ranks nth];lia) Upper).
 - exact(reference_rs2_types_history invalid history limit 200 Steps Source 75%nat ltac:(vm_compute;lia) time ltac:(cbv [reference_rs2_rank reference_rs2_ranks nth];lia) Upper).
 }
 destruct n as [|n]. { split.
 - exact(reference_rs2_types_history invalid history limit 200 Steps Source 42%nat ltac:(vm_compute;lia) time ltac:(cbv [reference_rs2_rank reference_rs2_ranks nth];lia) Upper).
 - exact(reference_rs2_types_history invalid history limit 200 Steps Source 76%nat ltac:(vm_compute;lia) time ltac:(cbv [reference_rs2_rank reference_rs2_ranks nth];lia) Upper).
 }
 destruct n as [|n]. { split.
 - exact(reference_rs2_types_history invalid history limit 200 Steps Source 41%nat ltac:(vm_compute;lia) time ltac:(cbv [reference_rs2_rank reference_rs2_ranks nth];lia) Upper).
 - exact(reference_rs2_types_history invalid history limit 200 Steps Source 77%nat ltac:(vm_compute;lia) time ltac:(cbv [reference_rs2_rank reference_rs2_ranks nth];lia) Upper).
 }
 destruct n as [|n]. { split.
 - exact(reference_rs2_types_history invalid history limit 200 Steps Source 40%nat ltac:(vm_compute;lia) time ltac:(cbv [reference_rs2_rank reference_rs2_ranks nth];lia) Upper).
 - exact(reference_rs2_types_history invalid history limit 200 Steps Source 78%nat ltac:(vm_compute;lia) time ltac:(cbv [reference_rs2_rank reference_rs2_ranks nth];lia) Upper).
 }
 destruct n as [|n]. { split.
 - exact(reference_rs2_types_history invalid history limit 200 Steps Source 39%nat ltac:(vm_compute;lia) time ltac:(cbv [reference_rs2_rank reference_rs2_ranks nth];lia) Upper).
 - exact(reference_rs2_types_history invalid history limit 200 Steps Source 79%nat ltac:(vm_compute;lia) time ltac:(cbv [reference_rs2_rank reference_rs2_ranks nth];lia) Upper).
 }
 destruct n as [|n]. { split.
 - exact(reference_rs2_types_history invalid history limit 200 Steps Source 38%nat ltac:(vm_compute;lia) time ltac:(cbv [reference_rs2_rank reference_rs2_ranks nth];lia) Upper).
 - exact(reference_rs2_types_history invalid history limit 200 Steps Source 80%nat ltac:(vm_compute;lia) time ltac:(cbv [reference_rs2_rank reference_rs2_ranks nth];lia) Upper).
 }
 destruct n as [|n]. { split.
 - exact(reference_rs2_types_history invalid history limit 200 Steps Source 37%nat ltac:(vm_compute;lia) time ltac:(cbv [reference_rs2_rank reference_rs2_ranks nth];lia) Upper).
 - exact(reference_rs2_types_history invalid history limit 200 Steps Source 81%nat ltac:(vm_compute;lia) time ltac:(cbv [reference_rs2_rank reference_rs2_ranks nth];lia) Upper).
 }
 destruct n as [|n]. { split.
 - exact(reference_rs2_types_history invalid history limit 200 Steps Source 36%nat ltac:(vm_compute;lia) time ltac:(cbv [reference_rs2_rank reference_rs2_ranks nth];lia) Upper).
 - exact(reference_rs2_types_history invalid history limit 200 Steps Source 82%nat ltac:(vm_compute;lia) time ltac:(cbv [reference_rs2_rank reference_rs2_ranks nth];lia) Upper).
 }
 destruct n as [|n]. { split.
 - exact(reference_rs2_types_history invalid history limit 200 Steps Source 35%nat ltac:(vm_compute;lia) time ltac:(cbv [reference_rs2_rank reference_rs2_ranks nth];lia) Upper).
 - exact(reference_rs2_types_history invalid history limit 200 Steps Source 83%nat ltac:(vm_compute;lia) time ltac:(cbv [reference_rs2_rank reference_rs2_ranks nth];lia) Upper).
 }
 destruct n as [|n]. { split.
 - exact(reference_rs2_types_history invalid history limit 200 Steps Source 34%nat ltac:(vm_compute;lia) time ltac:(cbv [reference_rs2_rank reference_rs2_ranks nth];lia) Upper).
 - exact(reference_rs2_types_history invalid history limit 200 Steps Source 84%nat ltac:(vm_compute;lia) time ltac:(cbv [reference_rs2_rank reference_rs2_ranks nth];lia) Upper).
 }
 destruct n as [|n]. { split.
 - exact(reference_rs2_types_history invalid history limit 200 Steps Source 33%nat ltac:(vm_compute;lia) time ltac:(cbv [reference_rs2_rank reference_rs2_ranks nth];lia) Upper).
 - exact(reference_rs2_types_history invalid history limit 200 Steps Source 85%nat ltac:(vm_compute;lia) time ltac:(cbv [reference_rs2_rank reference_rs2_ranks nth];lia) Upper).
 }
 lia. Qed.
Definition reference_store_rs2_aux_ids : seq VarOrder.T := [::1942;2575;1947;2576;1952;2577;2621;2622].
Definition reference_store_rs2_aux_node i := nth 0 reference_store_rs2_aux_ids i.
Definition reference_store_rs2_aux_expressions := [::reference_control_expr_1942;reference_control_expr_2575;reference_control_expr_1947;reference_control_expr_2576;reference_control_expr_1952;reference_control_expr_2577;reference_control_expr_2621;reference_control_expr_2622].
Definition reference_store_rs2_aux_expression i := nth (@Econst VarOrder.T (Fuint 1)[::false]) reference_store_rs2_aux_expressions i.
Lemma reference_store_rs2_aux_value i inputs path history limit reset time width word : (i<8)%coq_nat ->
 (forall t,(t<=limit)%coq_nat ->VM.find 1(history t)=Some(Gval(Fuint 1)[::reset])) ->
 (forall t,(t<limit)%coq_nat ->formal_value_iter(formal_invalid_policy inputs path)flat_memories(history t)false(history t)flat_statements=Some(history(S t))) ->
 (500<=time)%coq_nat ->(time<limit)%coq_nat ->
 (forall site,eval_hfexpr_validif_policy(isolated_validif_policy(formal_invalid_policy inputs path))site flat_memories(reference_store_rs2_aux_expression i)(history time)(history time)=Some(Gval(Fuint width)word)) ->
 VM.find(reference_store_rs2_aux_node i)(history time)=Some(Gval(Fuint width)word).
Proof. intros Bound Resets Steps Lower Upper Eval.
 destruct i as [|i].
 { change (VM.find 1942(history time)=Some(Gval(Fuint width)word)).
 rewrite(reference_control_stable_1942_history inputs path history limit reset Resets Steps time(S time)ltac:(lia)ltac:(lia)ltac:(lia)ltac:(lia)).
 eapply(reference_redirect_ground_step reference_control_0_offsets reference_control_0_nodes 1942 reference_control_expr_1942);[exact reference_control_0_positions|exact reference_control_0_safety|exact reference_control_member_1942|exact Eval|apply Steps;lia]. }
 destruct i as [|i].
 { change (VM.find 2575(history time)=Some(Gval(Fuint width)word)).
 rewrite(reference_control_stable_2575_history inputs path history limit reset Resets Steps time(S time)ltac:(lia)ltac:(lia)ltac:(lia)ltac:(lia)).
 eapply(reference_redirect_ground_step reference_control_2_offsets reference_control_2_nodes 2575 reference_control_expr_2575);[exact reference_control_2_positions|exact reference_control_2_safety|exact reference_control_member_2575|exact Eval|apply Steps;lia]. }
 destruct i as [|i].
 { change (VM.find 1947(history time)=Some(Gval(Fuint width)word)).
 rewrite(reference_control_stable_1947_history inputs path history limit reset Resets Steps time(S time)ltac:(lia)ltac:(lia)ltac:(lia)ltac:(lia)).
 eapply(reference_redirect_ground_step reference_control_0_offsets reference_control_0_nodes 1947 reference_control_expr_1947);[exact reference_control_0_positions|exact reference_control_0_safety|exact reference_control_member_1947|exact Eval|apply Steps;lia]. }
 destruct i as [|i].
 { change (VM.find 2576(history time)=Some(Gval(Fuint width)word)).
 rewrite(reference_control_stable_2576_history inputs path history limit reset Resets Steps time(S time)ltac:(lia)ltac:(lia)ltac:(lia)ltac:(lia)).
 eapply(reference_redirect_ground_step reference_control_2_offsets reference_control_2_nodes 2576 reference_control_expr_2576);[exact reference_control_2_positions|exact reference_control_2_safety|exact reference_control_member_2576|exact Eval|apply Steps;lia]. }
 destruct i as [|i].
 { change (VM.find 1952(history time)=Some(Gval(Fuint width)word)).
 rewrite(reference_control_stable_1952_history inputs path history limit reset Resets Steps time(S time)ltac:(lia)ltac:(lia)ltac:(lia)ltac:(lia)).
 eapply(reference_redirect_ground_step reference_control_0_offsets reference_control_0_nodes 1952 reference_control_expr_1952);[exact reference_control_0_positions|exact reference_control_0_safety|exact reference_control_member_1952|exact Eval|apply Steps;lia]. }
 destruct i as [|i].
 { change (VM.find 2577(history time)=Some(Gval(Fuint width)word)).
 rewrite(reference_control_stable_2577_history inputs path history limit reset Resets Steps time(S time)ltac:(lia)ltac:(lia)ltac:(lia)ltac:(lia)).
 eapply(reference_redirect_ground_step reference_control_2_offsets reference_control_2_nodes 2577 reference_control_expr_2577);[exact reference_control_2_positions|exact reference_control_2_safety|exact reference_control_member_2577|exact Eval|apply Steps;lia]. }
 destruct i as [|i].
 { change (VM.find 2621(history time)=Some(Gval(Fuint width)word)).
 rewrite(reference_control_stable_2621_history inputs path history limit reset Resets Steps time(S time)ltac:(lia)ltac:(lia)ltac:(lia)ltac:(lia)).
 eapply(reference_redirect_ground_step reference_control_2_offsets reference_control_2_nodes 2621 reference_control_expr_2621);[exact reference_control_2_positions|exact reference_control_2_safety|exact reference_control_member_2621|exact Eval|apply Steps;lia]. }
 destruct i as [|i].
 { change (VM.find 2622(history time)=Some(Gval(Fuint width)word)).
 rewrite(reference_control_stable_2622_history inputs path history limit reset Resets Steps time(S time)ltac:(lia)ltac:(lia)ltac:(lia)ltac:(lia)).
 eapply(reference_redirect_ground_step reference_control_2_offsets reference_control_2_nodes 2622 reference_control_expr_2622);[exact reference_control_2_positions|exact reference_control_2_safety|exact reference_control_member_2622|exact Eval|apply Steps;lia]. }
 lia. Qed.
Lemma reference_store_rs2_raw inputs path history limit reset time instruction lane :
 (lane<3)%coq_nat ->
 (forall t,(t<=limit)%coq_nat ->VM.find 1(history t)=Some(Gval(Fuint 1)[::reset])) ->
 (forall t,(t<limit)%coq_nat ->formal_value_iter(formal_invalid_policy inputs path)flat_memories(history t)false(history t)flat_statements=Some(history(S t))) ->
 (500<=time)%coq_nat ->(time<limit)%coq_nat ->
 VM.find 1884(history time)=Some(Gval(Fuint 32)instruction) ->
 VM.find(reference_store_rs2_yes(Nat.sub 2 lane))(history time)=Some(Gval(Fuint 5)(rf_instruction_address true instruction)).
Proof.
 intros Lane Resets Steps Lower Upper Source.
 destruct lane as [|lane]. {
 assert(V0:VM.find 1942(history time)=Some(Gval(Fuint 25)(take 25 instruction))).
 { eapply(reference_store_rs2_aux_value 0 inputs path history limit reset time);[lia|exact Resets|exact Steps|exact Lower|exact Upper|].
 intro site. cbn [reference_store_rs2_aux_expression reference_store_rs2_aux_expressions nth reference_control_expr_1942 eval_hfexpr_validif_policy eval_href_validif_policy]. rewrite Source. cbn.
 repeat rewrite drop0. repeat rewrite <- take_min. cbn. reflexivity. }
 assert(V1:VM.find 2575(history time)=Some(Gval(Fuint 5)(rf_instruction_address true instruction))).
 { eapply(reference_store_rs2_aux_value 1 inputs path history limit reset time);[lia|exact Resets|exact Steps|exact Lower|exact Upper|].
 intro site. cbn [reference_store_rs2_aux_expression reference_store_rs2_aux_expressions nth reference_control_expr_2575 eval_hfexpr_validif_policy eval_href_validif_policy]. rewrite V0. cbn.
 unfold rf_instruction_address.
 repeat rewrite drop0. repeat rewrite <- take_min. cbn. reflexivity. }
 exact V1. }
 destruct lane as [|lane]. {
 assert(V0:VM.find 1947(history time)=Some(Gval(Fuint 25)(take 25 instruction))).
 { eapply(reference_store_rs2_aux_value 2 inputs path history limit reset time);[lia|exact Resets|exact Steps|exact Lower|exact Upper|].
 intro site. cbn [reference_store_rs2_aux_expression reference_store_rs2_aux_expressions nth reference_control_expr_1947 eval_hfexpr_validif_policy eval_href_validif_policy]. rewrite Source. cbn.
 repeat rewrite drop0. repeat rewrite <- take_min. cbn. reflexivity. }
 assert(V1:VM.find 2576(history time)=Some(Gval(Fuint 5)(rf_instruction_address true instruction))).
 { eapply(reference_store_rs2_aux_value 3 inputs path history limit reset time);[lia|exact Resets|exact Steps|exact Lower|exact Upper|].
 intro site. cbn [reference_store_rs2_aux_expression reference_store_rs2_aux_expressions nth reference_control_expr_2576 eval_hfexpr_validif_policy eval_href_validif_policy]. rewrite V0. cbn.
 unfold rf_instruction_address.
 repeat rewrite drop0. repeat rewrite <- take_min. cbn. reflexivity. }
 exact V1. }
 destruct lane as [|lane]. {
 assert(V0:VM.find 1952(history time)=Some(Gval(Fuint 25)(take 25 instruction))).
 { eapply(reference_store_rs2_aux_value 4 inputs path history limit reset time);[lia|exact Resets|exact Steps|exact Lower|exact Upper|].
 intro site. cbn [reference_store_rs2_aux_expression reference_store_rs2_aux_expressions nth reference_control_expr_1952 eval_hfexpr_validif_policy eval_href_validif_policy]. rewrite Source. cbn.
 repeat rewrite drop0. repeat rewrite <- take_min. cbn. reflexivity. }
 assert(V1:VM.find 2577(history time)=Some(Gval(Fuint 5)(rf_instruction_address true instruction))).
 { eapply(reference_store_rs2_aux_value 5 inputs path history limit reset time);[lia|exact Resets|exact Steps|exact Lower|exact Upper|].
 intro site. cbn [reference_store_rs2_aux_expression reference_store_rs2_aux_expressions nth reference_control_expr_2577 eval_hfexpr_validif_policy eval_href_validif_policy]. rewrite V0. cbn.
 unfold rf_instruction_address.
 repeat rewrite drop0. repeat rewrite <- take_min. cbn. reflexivity. }
 exact V1. }
 lia. Qed.
Theorem reference_store_rs2_history inputs path history limit reset time instruction lane :
 (lane<3)%coq_nat ->size instruction=32%nat ->
 (forall t,(t<=limit)%coq_nat ->VM.find 1(history t)=Some(Gval(Fuint 1)[::reset])) ->
 (forall t,(t<limit)%coq_nat ->formal_value_iter(formal_invalid_policy inputs path)flat_memories(history t)false(history t)flat_statements=Some(history(S t))) ->
 (forall t,(200<=t)%coq_nat ->(t<=limit)%coq_nat ->VM.find 1884(history t)=Some(Gval(Fuint 32)instruction)) ->
 (500<=time)%coq_nat ->(time<limit)%coq_nat ->
 VM.find 1707(history time)=Some(Gval(Fuint 1)[::true]) ->
 (forall n,(n<11)%coq_nat ->VM.find(reference_store_rs2_guard n)(history time)=Some(Gval(Fuint 1)[::Nat.eqb n(Nat.sub 2 lane)])) ->
 VM.find 2622(history time)=Some(Gval(Fuint 5)(rf_instruction_address true instruction)).
Proof.
 intros Lane Size Resets Steps Source Lower Upper Enabled Guards.
 assert (TypedSource : forall t,(200<=t)%coq_nat ->(t<=limit)%coq_nat ->exists v,VM.find 1884(history t)=Some v /\type_of_val v=Gtyp(Fuint 32)).
 { intros t L U. exists(Gval(Fuint 32)instruction);split;[apply Source;assumption|reflexivity]. }
 pose proof(reference_store_rs2_raw inputs path history limit reset time instruction lane Lane Resets Steps Lower Upper (Source time ltac:(lia)ltac:(lia))) as Raw.
 assert (Selected : VM.find 2620(history time)=Some(Gval(Fuint 5)(rf_instruction_address true instruction))).
 { change (VM.find(reference_store_rs2_node 10)(history time)=Some(Gval(Fuint 5)(rf_instruction_address true instruction))).
 eapply(immediate_stable_mux_suffix (formal_invalid_policy inputs path)(history time)(history(S time)) 11 (Nat.sub 2 lane) 5 (rf_instruction_address true instruction) 2609 reference_store_rs2_node reference_store_rs2_guard reference_store_rs2_yes);[lia|exact(rf_instruction_address_size true instruction Size)| | |exact Guards| | |exact Raw|lia|lia].
 - intros n Bound. exact(reference_store_rs2_same n inputs path history limit reset time Bound Resets Steps Lower Upper).
 - intros n Bound value Eval. apply(reference_store_rs2_step n _ _ _ value Bound Eval);apply Steps;exact Upper.
 - intros n Bound. exact(proj1(reference_store_rs2_branch_types n _ history limit time Bound Steps TypedSource Lower ltac:(lia))).
 - intros n Bound. exact(proj2(reference_store_rs2_branch_types n _ history limit time Bound Steps TypedSource Lower ltac:(lia))). }
 assert (Gate : VM.find 2621(history time)=Some(Gval(Fuint 5)(rf_instruction_address true instruction))).
 { eapply(reference_store_rs2_aux_value 6 inputs path history limit reset time);[lia|exact Resets|exact Steps|exact Lower|exact Upper|]. intro site.
 cbn [reference_store_rs2_aux_expression reference_store_rs2_aux_expressions nth reference_control_expr_2621 eval_hfexpr_validif_policy eval_href_validif_policy]. rewrite Enabled;cbn;rewrite Selected. apply dut_decode_adapt;exact(rf_instruction_address_size true instruction Size). }
 eapply(reference_store_rs2_aux_value 7 inputs path history limit reset time);[lia|exact Resets|exact Steps|exact Lower|exact Upper|]. intro site;exact Gate.
Qed.
(* Store rs2 observed composition. *)
Require Import ReferenceStoreObserved StoreTypeCorrespondence RFScalarControl RFReferenceNopHistory FormalObservedHistory ObservedJointRegisterConcrete JointUpdateBoundaryHistory FormalLocalHistory MemoryRequestObservedSemantics.
Lemma reference_store_rs2_decode instruction lane n : (lane<3)%coq_nat ->(n<11)%coq_nat ->store_type_is_store instruction lane ->
 N.eqb(reference_instruction_code(reference_store_rs2_decoder n))(N.land(to_N instruction)(reference_instruction_mask(reference_store_rs2_decoder n)))=Nat.eqb n(Nat.sub 2 lane).
Proof.
 intros Lane Bound Store.
 assert (Match : N.land (to_N instruction) (reference_instruction_mask (Nat.sub 36 lane)) = reference_instruction_code (Nat.sub 36 lane)).
 { unfold store_type_is_store in Store. do 3 (destruct lane as [|lane];[exact Store|]);lia. }
 rewrite (rf_reference_decode_onehot instruction (Nat.sub 36 lane) (reference_store_rs2_decoder n) ltac:(lia) ltac:(do 11 (destruct n as [|n];[cbn [reference_store_rs2_decoder nth];lia|]);lia) Match).
 do 3 (destruct lane as [|lane];[do 11 (destruct n as [|n];[reflexivity|]);lia|]);lia.
Qed.
Theorem reference_store_rs2_observed memory inputs k observed instruction lane :
 generated_observe memory inputs k = Some observed -> generated_legal_trace memory inputs k ->
 VM.find 1 (formal_external_inputs (generated_observation_input inputs k)) = Some (Gval (Fuint 1) [::false]) ->
 (lane < 3)%coq_nat -> VM.find 7750 (top_environment observed) = Some (Gval (Fuint 32) instruction) ->
 store_type_is_store instruction lane ->
 VM.find 2622 (top_environment observed) = Some (Gval (Fuint 5) (rf_instruction_address true instruction)).
Proof.
 intros Observe Legal Reset Lane Instruction Load.
 pose proof (store_reference_enabled_observed memory inputs k observed instruction lane Observe Legal Reset Lane Instruction Load) as Enabled.
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
 assert (Guards : forall n,(n<11)%coq_nat ->VM.find(reference_store_rs2_guard n)(history 9250%nat)=Some(Gval(Fuint 1)[::Nat.eqb n(Nat.sub 2 lane)])).
 { intros n Bound.
   set (h := fun t:nat => history (match t with O=>9248%nat | S O=>9249%nat | _=>9250%nat end)).
   assert (HS : forall t,(t<2)%coq_nat ->formal_value_iter(formal_invalid_policy(generated_observation_input inputs k)nil)flat_memories(h t)false(h t)flat_statements=Some(h(S t))).
   { intros [|[|t]] T;[apply Steps;vm_compute;lia|apply Steps;vm_compute;lia|lia]. }
   assert (HI : forall t,(t<=2)%coq_nat ->VM.find 1884(h t)=Some(Gval(Fuint 32)instruction)).
   { intros [|[|t]] T;unfold h;apply Source;vm_compute;lia. }
   pose proof(reference_instruction_decode_history _ h 2 instruction (reference_store_rs2_decoder n) ltac:(do 11 (destruct n as [|n];[cbn [reference_store_rs2_decoder nth];lia|]);lia) HS HI 2 ltac:(lia) ltac:(lia))as Decode.
   rewrite(reference_store_rs2_decode instruction lane n Lane Bound Load)in Decode. exact Decode. }
 pose proof(reference_store_rs2_history (generated_observation_input inputs k)nil history 9259 reset 9250 instruction lane Lane Size Resets Steps Source ltac:(vm_compute;lia)ltac:(vm_compute;lia)(Enable 9250%nat ltac:(vm_compute;lia)ltac:(vm_compute;lia))Guards)as Value.
 rewrite(reference_control_stable_2622_history (generated_observation_input inputs k)nil history 9259 reset Resets Steps 9250 9259 ltac:(vm_compute;lia)ltac:(vm_compute;lia)ltac:(vm_compute;lia)ltac:(vm_compute;lia))Last in Value. exact Value.
Qed.
Theorem reference_store_rs2_bank_observed memory inputs k observed instruction lane bank :
 generated_observe memory inputs k=Some observed ->generated_legal_trace memory inputs k ->
 VM.find 1(formal_external_inputs(generated_observation_input inputs k))=Some(Gval(Fuint 1)[::false]) ->
 (lane<3)%coq_nat ->VM.find 7750(top_environment observed)=Some(Gval(Fuint 32)instruction) ->store_type_is_store instruction lane ->
 rf_reference_bank_at(top_environment observed)bank ->
 VM.find 2804(top_environment observed)=Some(Gval(Fuint 32)(bank(to_nat(rf_instruction_address true instruction)))).
Proof.
 intros Observe Legal Reset Lane Instruction Load Bank.
 assert(Size:size instruction=32%nat).
 { destruct(observed_joint_register_concrete memory inputs k observed 7750%nat 32%nat Observe Legal load_type_instruction_member)as[word[W V]]. rewrite Instruction in V;inversion V;subst;exact W. }
 eapply(reference_second_register_read_observed memory inputs k observed bank (rf_instruction_address true instruction));[exact Observe|exact Legal|exact Bank|exact(rf_instruction_address_size true instruction Size)|].
 exact(reference_store_rs2_observed memory inputs k observed instruction lane Observe Legal Reset Lane Instruction Load).
Qed.
